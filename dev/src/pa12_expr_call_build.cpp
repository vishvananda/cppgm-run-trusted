#include "pa12_expr_semantics_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

bool builtin_bswap_width(const string& name, unsigned& bits)
{
	if (name == "__builtin_bswap16")
	{
		bits = 16;
		return true;
	}
	if (name == "__builtin_bswap32")
	{
		bits = 32;
		return true;
	}
	if (name == "__builtin_bswap64")
	{
		bits = 64;
		return true;
	}
	return false;
}

uint64_t byte_swap_value(uint64_t value, unsigned bits)
{
	uint64_t out = 0;
	unsigned bytes = bits / 8;
	for (unsigned i = 0; i < bytes; ++i)
	{
		out <<= 8;
		out |= (value >> (i * 8)) & 0xffu;
	}
	return out;
}

bool builtin_bit_count_name(const string& name)
{
	return name == "__builtin_clz" ||
	       name == "__builtin_clzl" ||
	       name == "__builtin_clzll" ||
	       name == "__builtin_clzg" ||
	       name == "__builtin_ctz" ||
	       name == "__builtin_ctzl" ||
	       name == "__builtin_ctzll" ||
	       name == "__builtin_popcount" ||
	       name == "__builtin_popcountl" ||
	       name == "__builtin_popcountll" ||
	       name == "__builtin_popcountg";
}

bool source_location_builtin_name(const string& name)
{
	return name == "__builtin_FILE" ||
	       name == "__builtin_FUNCTION" ||
	       name == "__builtin_LINE" ||
	       name == "__builtin_COLUMN";
}

unsigned builtin_bit_count_width(const string& name, TypePtr arg_type)
{
	if (name == "__builtin_clz" ||
	    name == "__builtin_ctz" ||
	    name == "__builtin_popcount")
		return 32;
	if (name == "__builtin_clzl" ||
	    name == "__builtin_ctzl" ||
	    name == "__builtin_popcountl")
		return static_cast<unsigned>(
			pa11::type_size(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)) * 8);
	if (name == "__builtin_clzll" ||
	    name == "__builtin_ctzll" ||
	    name == "__builtin_popcountll")
		return 64;
	return static_cast<unsigned>(
		pa11::type_size(pa11::strip_cv(arg_type)) * 8);
}

uint64_t bit_mask_for_width(unsigned width)
{
	return width >= 64 ? ~uint64_t(0) : ((uint64_t(1) << width) - 1);
}

uint64_t count_leading_zeroes(uint64_t value, unsigned width)
{
	value &= bit_mask_for_width(width);
	if (value == 0)
		return width;
	uint64_t count = 0;
	for (int bit = static_cast<int>(width) - 1; bit >= 0; --bit)
	{
		if ((value & (uint64_t(1) << bit)) != 0)
			break;
		++count;
	}
	return count;
}

uint64_t count_trailing_zeroes(uint64_t value, unsigned width)
{
	value &= bit_mask_for_width(width);
	if (value == 0)
		return width;
	uint64_t count = 0;
	while ((value & 1) == 0)
	{
		++count;
		value >>= 1;
	}
	return count;
}

uint64_t count_population(uint64_t value, unsigned width)
{
	value &= bit_mask_for_width(width);
	uint64_t count = 0;
	while (value != 0)
	{
		count += value & 1;
		value >>= 1;
	}
	return count;
}

bool c11_atomic_builtin_name(const string& name)
{
	return name == "__c11_atomic_load" ||
	       name == "__c11_atomic_init" ||
	       name == "__c11_atomic_store" ||
	       name == "__c11_atomic_exchange" ||
	       name == "__c11_atomic_compare_exchange_strong" ||
	       name == "__c11_atomic_compare_exchange_weak" ||
	       name == "__c11_atomic_fetch_add" ||
	       name == "__c11_atomic_fetch_sub" ||
	       name == "__c11_atomic_fetch_and" ||
	       name == "__c11_atomic_fetch_or" ||
	       name == "__c11_atomic_fetch_xor" ||
	       name == "__c11_atomic_is_lock_free" ||
	       name == "__c11_atomic_thread_fence" ||
	       name == "__c11_atomic_signal_fence";
}

bool scope_is_namespace_named(Scope* scope, const string& name)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == name)
			return true;
	return false;
}

bool hosted_std_tuple_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return false;
	if (bare->scope != NULL &&
	    bare->scope->name == "tuple" &&
	    scope_is_namespace_named(bare->scope->parent, "std"))
		return true;
	return bare->template_primary_name == "std::tuple" ||
	       bare->template_primary_name == "tuple";
}

void complete_hosted_reference_tuple_layout(TypePtr type, size_t references)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    !hosted_std_tuple_record(bare) ||
	    bare->complete)
		return;
	uint64_t size = references == 0 ? 1 : references * 8;
	bare->complete = true;
	bare->fields.clear();
	bare->direct_bases.clear();
	bare->direct_base_offsets.clear();
	bare->direct_base_virtuals.clear();
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->direct_base_offset = 0;
	bare->record_size = size;
	bare->record_align = references == 0 ? 1 : 8;
	bare->nonvirtual_size = size;
	bare->nonvirtual_align = bare->record_align;
	bare->layout_valid = true;
}

bool gnu_atomic_builtin_name(const string& name)
{
	return name == "__atomic_load_n" ||
	       name == "__atomic_load" ||
	       name == "__atomic_store_n" ||
	       name == "__atomic_store" ||
	       name == "__atomic_exchange_n" ||
	       name == "__atomic_compare_exchange" ||
	       name == "__atomic_compare_exchange_n" ||
	       name == "__atomic_fetch_add" ||
	       name == "__atomic_fetch_sub" ||
	       name == "__atomic_fetch_and" ||
	       name == "__atomic_fetch_or" ||
	       name == "__atomic_fetch_xor" ||
	       name == "__atomic_add_fetch" ||
	       name == "__atomic_sub_fetch" ||
	       name == "__atomic_and_fetch" ||
	       name == "__atomic_or_fetch" ||
	       name == "__atomic_xor_fetch" ||
	       name == "__atomic_always_lock_free" ||
	       name == "__atomic_is_lock_free" ||
	       name == "__atomic_thread_fence" ||
	       name == "__atomic_signal_fence" ||
	       name == "__atomic_test_and_set" ||
	       name == "__atomic_clear" ||
	       name == "__sync_lock_test_and_set" ||
	       name == "__sync_lock_release";
}

bool overflow_builtin_name(const string& name)
{
	return name == "__builtin_add_overflow" ||
	       name == "__builtin_sub_overflow" ||
	       name == "__builtin_mul_overflow";
}

bool float_constant_builtin_name(const string& name)
{
	return name == "__builtin_inf" ||
	       name == "__builtin_inff" ||
	       name == "__builtin_infl" ||
	       name == "__builtin_huge_val" ||
	       name == "__builtin_huge_valf" ||
	       name == "__builtin_huge_vall" ||
	       name == "__builtin_nan" ||
	       name == "__builtin_nanf" ||
	       name == "__builtin_nanl" ||
	       name == "__builtin_nans" ||
	       name == "__builtin_nansf" ||
	       name == "__builtin_nansl";
}

Expr make_direct_builtin_call(Binding* binding,
                              TypePtr result,
                              const vector<Expr>& args,
                              ValueCategory category = ValueCategory::PRValue)
{
	string category_name = category == ValueCategory::LValue
		? "lvalue" : category == ValueCategory::XValue ? "xvalue" : "prvalue";
	Expr out;
	out.valid = true;
	out.type = result;
	out.category = category;
	out.node = Node("call-expression " + category_name +
	                " " + pa11::describe_type(out.type));
	out.node.direct_call = binding;
	Node callee_node("callee " + binding->name +
	                 " " + pa11::describe_type(binding->type));
	callee_node.binding = binding;
	callee_node.direct_call = binding;
	add_child(out.node, callee_node);
	for (size_t i = 0; i < args.size(); ++i)
		add_child(out.node, args[i].node);
	annotate_expr_node(out);
	return out;
}

TypePtr atomic_pointee_type(const Expr& arg)
{
	TypePtr type = pa11::strip_cv(arg.type);
	if (type->kind != pa11::TypeKind::Pointer)
		throw runtime_error("atomic argument is not pointer");
	return pa11::strip_cv(type->base);
}

}  // namespace

bool Parser::make_member_pointer_call_expr(const Expr& callee,
                                           const vector<Expr>& args,
                                           Expr& out)
{
	if (callee.node.line.compare(0, 34,
	                             "member-pointer-function-expression") != 0)
		return false;
	TypePtr callee_type = expression_object_type(callee.type);
	callee_type = pa11::strip_cv(callee_type);
	if (callee_type->kind == pa11::TypeKind::Pointer)
		callee_type = callee_type->base;
	if (callee_type->kind != pa11::TypeKind::Function ||
	    callee_type->parameters.empty() ||
	    callee.node.children.size() < 2)
		throw runtime_error("member pointer call target is not callable");
	if (args.size() + 1 != callee_type->parameters.size() &&
	    !callee_type->variadic)
		throw runtime_error("wrong argument count");
	Expr object;
	object.valid = true;
	object.node = callee.node.children[0];
	object.type = object.node.type;
	object.category = object.node.category;
	object.binding = object.node.binding;
	vector<Expr> converted;
	converted.push_back(callee.node.has_op && callee.node.op == OP_ARROWSTAR
	                    ? object : make_address_expr("&", object));
	converted.insert(converted.end(), args.begin(), args.end());
	for (size_t i = 0; i < callee_type->parameters.size(); ++i)
	{
		Conversion conv = convert_to(converted[i], callee_type->parameters[i]);
		if (!conv.viable)
			throw runtime_error("invalid argument conversion");
		converted[i] = conv.expr;
	}
	out.type = callee_type->base;
	out.category = call_category(out.type);
	out.node = Node("call-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type));
	add_child(out.node, callee.node);
		for (size_t i = 0; i < converted.size(); ++i)
			add_child(out.node, converted[i].node);
		out.valid = true;
		if (unevaluated_expression_depth_ == 0 &&
		    out.category == ValueCategory::PRValue &&
		    pa11::strip_cv(out.type)->kind == pa11::TypeKind::Record &&
		    !type_is_template_dependent(out.type))
			ensure_default_destructor(out.type);
	annotate_expr_node(out);
	return true;
}

bool Parser::make_record_callable_call_expr(const Expr& callee,
                                            const vector<Expr>& args,
                                            Expr& out)
{
	TypePtr callee_object = pa11::strip_cv(expression_object_type(callee.type));
	if (!callee.overloads.empty() ||
	    callee_object->kind != pa11::TypeKind::Record ||
	    callee_object->scope == NULL)
		return false;
	vector<Binding*> members =
		lookup_qualified_set(callee_object->scope,
		                     "operator()",
		                     pa11::LOOKUP_FUNCTION);
	if (!members.empty())
	{
		Expr member = make_member_expr(callee, "operator()", ".");
		out = make_call_expr(member, args);
		return true;
	}
	vector<Binding*> conversions;
	set<Scope*> seen;
	collect_conversion_functions(callee_object, seen, conversions);
	bool ambiguous = false;
	for (size_t i = 0; i < conversions.size(); ++i)
	{
		Binding* op = conversions[i];
		if (op->kind != BindingKind::Function ||
		    op->type->kind != pa11::TypeKind::Function ||
		    op->type->parameters.size() != 1)
			continue;
		TypePtr result = pa11::strip_cv(op->type->base);
		if (result->kind != pa11::TypeKind::Pointer ||
		    result->base.get() == NULL ||
		    result->base->kind != pa11::TypeKind::Function)
			continue;
		try
		{
			Expr member = make_member_expr(callee, op->name, ".");
			member.overloads.clear();
			member.overloads.push_back(op);
			member.binding = op;
			member.type = op->type;
			Expr converted = make_call_expr(member, vector<Expr>());
			Expr call = make_call_expr(converted, args);
			if (!out.valid)
				out = call;
			else
				ambiguous = true;
		}
		catch (const runtime_error&)
		{
		}
	}
	if (ambiguous)
		throw runtime_error("ambiguous surrogate call");
	return out.valid;
}

bool Parser::make_simple_builtin_call_expr(const Expr& callee,
                                           const vector<Expr>& args,
                                           Expr& out)
{
	if (callee.builtin_constant_p)
	{
		out = make_builtin_constant_call(args);
		return true;
	}
	if (callee.binding == NULL)
		return false;
	const string& name = callee.binding->name;
	if (name == "__builtin_is_constant_evaluated")
	{
		if (!args.empty())
			throw runtime_error("wrong argument count");
		out = make_integer_literal_expr(FT_BOOL, 0);
		return true;
	}
	if (name == "__builtin_expect")
	{
		if (args.size() < 1 || args.size() > 2)
			throw runtime_error("wrong argument count");
		out = args[0];
		return true;
	}
	if (name == "__builtin_addressof")
	{
		if (args.size() != 1)
			throw runtime_error("wrong argument count");
		out = make_address_expr("&", args[0]);
		return true;
	}
	if (name == "__builtin_invoke")
	{
		if (args.empty())
			throw runtime_error("wrong argument count");
		TypePtr callable = pa11::strip_cv(expression_object_type(args[0].type));
		vector<Expr> rest(args.begin() + 1, args.end());
		if (callable->kind == pa11::TypeKind::MemberPointer)
		{
			if (args.size() < 2)
				throw runtime_error("wrong argument count");
			TypePtr object = pa11::strip_cv(expression_object_type(args[1].type));
			ETokenType op = object->kind == pa11::TypeKind::Pointer
				? OP_ARROWSTAR : OP_DOTSTAR;
			Expr target = make_binary_expr(op,
			                                op == OP_ARROWSTAR ? "->*" : ".*",
			                                args[1],
			                                args[0]);
			rest.erase(rest.begin());
			if (pa11::strip_cv(callable->base)->kind == pa11::TypeKind::Function)
				out = make_call_expr(target, rest);
			else
			{
				if (!rest.empty())
					throw runtime_error("wrong argument count");
				out = target;
			}
		}
		else
			out = make_call_expr(args[0], rest);
		return true;
	}
	if (source_location_builtin_name(name))
	{
		if (!args.empty())
			throw runtime_error("wrong argument count");
		if (name == "__builtin_LINE" || name == "__builtin_COLUMN")
			out = make_integer_literal_expr(FT_INT, 1);
		else if (name == "__builtin_FILE")
			out = make_string_literal_expr(tu_.srcfile);
		else
			out = make_string_literal_expr(active_functions_.empty()
			                               ? "" : active_functions_.back()->name);
		return true;
	}
	if (name == "__builtin_nanl")
	{
		if (args.size() != 1)
			throw runtime_error("wrong argument count");
		out.valid = true;
		out.type = pa11::make_fundamental(FT_LONG_DOUBLE);
		out.category = ValueCategory::PRValue;
		out.node = Node("builtin-nanl-expression prvalue " +
		                pa11::describe_type(out.type));
		add_child(out.node, args[0].node);
		return true;
	}
	if (name == "__builtin_isnan" &&
	    args.size() == 1 &&
	    args[0].node.line.compare(0, 23, "builtin-nanl-expression") == 0)
	{
		out = make_integer_literal_expr(FT_INT, 1);
		return true;
	}
	return false;
}

bool Parser::make_direct_hosted_builtin_call_expr(const Expr& callee,
                                                  const vector<Expr>& args,
                                                  Expr& out)
{
	if (callee.binding == NULL)
		return false;
	const string& name = callee.binding->name;
	if (name == "__builtin_assume_aligned")
	{
		if (args.size() < 2 || args.size() > 3)
			throw runtime_error("wrong argument count");
		out = make_direct_builtin_call(callee.binding,
		                               lvalue_to_rvalue_type(args[0].type),
		                               args);
		return true;
	}
	if (name == "__builtin_prefetch")
	{
		if (args.size() < 1 || args.size() > 3)
			throw runtime_error("wrong argument count");
		out = make_direct_builtin_call(callee.binding,
		                               pa11::make_fundamental(FT_VOID),
		                               args);
		return true;
	}
	if (name == "__builtin_operator_new" ||
	    name == "__builtin_operator_delete" ||
	    overflow_builtin_name(name) ||
	    name == "__builtin_flt_rounds" ||
	    name == "__builtin_fpclassify" ||
	    float_constant_builtin_name(name))
	{
		TypePtr result = callee.binding->type->base;
		if (name == "__builtin_operator_new")
			result = pa11::make_pointer(pa11::make_fundamental(FT_VOID));
		else if (name == "__builtin_operator_delete")
			result = pa11::make_fundamental(FT_VOID);
		else if (overflow_builtin_name(name))
			result = pa11::make_fundamental(FT_BOOL);
		else if (name == "__builtin_flt_rounds" ||
		         name == "__builtin_fpclassify")
			result = pa11::make_fundamental(FT_INT);
		bool needs_string = name == "__builtin_nan" ||
		                    name == "__builtin_nanf" ||
		                    name == "__builtin_nanl" ||
		                    name == "__builtin_nans" ||
		                    name == "__builtin_nansf" ||
		                    name == "__builtin_nansl";
		size_t wanted = name == "__builtin_fpclassify" ? 6 :
		                overflow_builtin_name(name) ? 3 :
		                (name == "__builtin_operator_new" ||
		                 name == "__builtin_operator_delete") ? 1 :
		                needs_string ? 1 : 0;
		if ((name == "__builtin_operator_new" ||
		     name == "__builtin_operator_delete")
		    ? args.empty() : args.size() != wanted)
			throw runtime_error("wrong argument count");
		out = make_direct_builtin_call(callee.binding, result, args);
		return true;
	}
	if (name == "__builtin_complex")
	{
		if (args.size() != 2)
			throw runtime_error("wrong argument count");
		out = make_direct_builtin_call(callee.binding,
		                               expression_object_type(args[0].type),
		                               args);
		return true;
	}
	return false;
}

bool Parser::make_bit_count_builtin_call_expr(const Expr& callee,
                                              const vector<Expr>& args,
                                              Expr& out)
{
	if (callee.binding == NULL ||
	    !builtin_bit_count_name(callee.binding->name))
		return false;
	const string& builtin = callee.binding->name;
	const bool clzg = builtin == "__builtin_clzg";
	if ((clzg && args.size() != 2) || (!clzg && args.size() != 1))
		throw runtime_error("wrong argument count");
	vector<Expr> converted = args;
	TypePtr target;
	if (builtin == "__builtin_clz" ||
	    builtin == "__builtin_ctz" ||
	    builtin == "__builtin_popcount")
		target = pa11::make_fundamental(FT_UNSIGNED_INT);
	else if (builtin == "__builtin_clzl" ||
	         builtin == "__builtin_ctzl" ||
	         builtin == "__builtin_popcountl")
		target = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
	else if (builtin == "__builtin_clzll" ||
	         builtin == "__builtin_ctzll" ||
	         builtin == "__builtin_popcountll")
		target = pa11::make_fundamental(FT_UNSIGNED_LONG_LONG_INT);
	if (target.get() != NULL)
	{
		Conversion conv = convert_to(args[0], target);
		if (!conv.viable)
			throw runtime_error("invalid argument conversion");
		converted[0] = conv.expr;
	}
	if (!pa11::is_integral_or_bool_type(pa11::strip_cv(
		    expression_object_type(converted[0].type))))
		throw runtime_error("invalid argument conversion");
	out = make_direct_builtin_call(callee.binding,
	                               pa11::make_fundamental(FT_INT),
	                               converted);
	if (converted[0].has_constant_value && (!clzg || converted[1].has_constant_value))
	{
		unsigned width =
			builtin_bit_count_width(builtin,
			                        expression_object_type(converted[0].type));
		uint64_t value = converted[0].constant_value;
		uint64_t result = 0;
		if (builtin.find("popcount") != string::npos)
			result = count_population(value, width);
		else if (builtin.find("ctz") != string::npos)
			result = count_trailing_zeroes(value, width);
		else if (clzg && (value & bit_mask_for_width(width)) == 0)
			result = converted[1].constant_value;
		else
			result = count_leading_zeroes(value, width);
		apply_constexpr_value(out, ConstexprValue::integer(result));
		out.node.token_text = to_string(result);
	}
	return true;
}

bool Parser::make_atomic_builtin_call_expr(const Expr& callee,
                                           const vector<Expr>& args,
                                           Expr& out)
{
	if (callee.binding == NULL)
		return false;
	const string& builtin = callee.binding->name;
	bool gnu = gnu_atomic_builtin_name(builtin);
	bool c11 = c11_atomic_builtin_name(builtin);
	if (!gnu && !c11)
		return false;
	TypePtr result = pa11::make_fundamental(FT_VOID);
	bool constant_lock_free =
		builtin == "__atomic_always_lock_free" ||
		builtin == "__atomic_is_lock_free" ||
		builtin == "__c11_atomic_is_lock_free";
	bool bool_result_builtin =
		constant_lock_free ||
		builtin == "__atomic_test_and_set" ||
		builtin == "__atomic_compare_exchange" ||
		builtin == "__atomic_compare_exchange_n";
	if (constant_lock_free)
		result = pa11::make_fundamental(FT_BOOL);
	if (bool_result_builtin)
		result = pa11::make_fundamental(FT_BOOL);
	else if (builtin == "__atomic_load_n" ||
	         builtin == "__atomic_exchange_n" ||
	         builtin == "__atomic_fetch_add" ||
	         builtin == "__atomic_fetch_sub" ||
	         builtin == "__atomic_fetch_and" ||
	         builtin == "__atomic_fetch_or" ||
	         builtin == "__atomic_fetch_xor" ||
	         builtin == "__atomic_add_fetch" ||
	         builtin == "__atomic_sub_fetch" ||
	         builtin == "__atomic_and_fetch" ||
	         builtin == "__atomic_or_fetch" ||
	         builtin == "__atomic_xor_fetch" ||
	         builtin == "__sync_lock_test_and_set" ||
	         builtin == "__c11_atomic_load" ||
	         builtin == "__c11_atomic_exchange" ||
	         builtin == "__c11_atomic_fetch_add" ||
	         builtin == "__c11_atomic_fetch_sub" ||
	         builtin == "__c11_atomic_fetch_and" ||
	         builtin == "__c11_atomic_fetch_or" ||
	         builtin == "__c11_atomic_fetch_xor")
	{
		if (args.empty())
			throw runtime_error("wrong argument count");
		result = atomic_pointee_type(args[0]);
	}
	else if (builtin == "__atomic_load" ||
	         builtin == "__atomic_store" ||
	         builtin == "__atomic_store_n" ||
	         builtin == "__atomic_clear" ||
	         builtin == "__sync_lock_release" ||
	         builtin == "__c11_atomic_init" ||
	         builtin == "__c11_atomic_store" ||
	         builtin == "__c11_atomic_compare_exchange_strong" ||
	         builtin == "__c11_atomic_compare_exchange_weak")
	{
		if (args.empty())
			throw runtime_error("wrong argument count");
		atomic_pointee_type(args[0]);
		if (builtin == "__c11_atomic_compare_exchange_strong" ||
		    builtin == "__c11_atomic_compare_exchange_weak")
			result = pa11::make_fundamental(FT_BOOL);
	}
	if (builtin == "__atomic_test_and_set" ||
	    builtin == "__atomic_compare_exchange" ||
	    builtin == "__atomic_compare_exchange_n")
	{
		if (args.empty())
			throw runtime_error("wrong argument count");
		atomic_pointee_type(args[0]);
	}
	out = make_direct_builtin_call(callee.binding, result, args);
	if (constant_lock_free)
	{
		apply_constexpr_value(out, ConstexprValue::integer(1));
		out.node.token_text = "1";
	}
	return true;
}

bool Parser::make_bswap_builtin_call_expr(const Expr& callee,
                                          const vector<Expr>& args,
                                          Expr& out)
{
	unsigned bswap_bits = 0;
	if (callee.binding == NULL ||
	    !builtin_bswap_width(callee.binding->name, bswap_bits))
		return false;
	if (args.size() != 1)
		throw runtime_error("wrong argument count");
	TypePtr result = callee.binding->type->base;
	Conversion conv = convert_to(args[0], result);
	if (!conv.viable)
		throw runtime_error("invalid argument conversion");
	out = make_direct_builtin_call(callee.binding, result, vector<Expr>(1, conv.expr));
	out.constant_expression = conv.expr.constant_expression;
	if (conv.expr.has_constant_value)
	{
		uint64_t value = byte_swap_value(conv.expr.constant_value, bswap_bits);
		apply_constexpr_value(out, ConstexprValue::integer(value));
		out.node.token_text = to_string(value);
	}
	return true;
}

void Parser::normalize_explicit_template_call_arguments(Expr& callee)
{
	for (map<Binding*, vector<TemplateArgument> >::iterator it =
		     callee.explicit_template_arguments.begin();
	     it != callee.explicit_template_arguments.end();
	     ++it)
	{
		vector<TemplateArgument> substituted;
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			vector<TemplateArgument> expanded =
				expand_template_argument_pack(it->second[i]);
			for (size_t j = 0; j < expanded.size(); ++j)
			{
				TemplateArgument arg = substitute_template_argument(expanded[j]);
				if (arg.kind == TemplateArgumentKind::Pack)
					substituted.insert(substituted.end(),
					                   arg.pack.begin(),
					                   arg.pack.end());
				else
					substituted.push_back(arg);
			}
		}
		it->second = substituted;
	}
}

bool Parser::call_is_dependent_template_call(const Expr& callee,
                                             const vector<Expr>& args)
{
	for (size_t i = 0; i < args.size(); ++i)
		if (args[i].overloads.empty() && type_is_template_dependent(args[i].type))
			return true;
	for (map<Binding*, vector<TemplateArgument> >::const_iterator it =
		     callee.explicit_template_arguments.begin();
	     it != callee.explicit_template_arguments.end();
	     ++it)
		if (template_arguments_dependent(it->second))
			return true;
	return false;
}

Binding* Parser::resolve_call_direct_binding(const Expr& callee,
                                             const vector<Expr>& args,
                                             vector<Expr>& converted)
{
	if (!callee.overloads.empty())
		return resolve_call_candidate(callee.overloads,
		                              args,
		                              callee.explicit_template_arguments,
		                              converted);
	if (callee.binding != NULL &&
	    callee.binding->kind == BindingKind::Function &&
	    is_lambda_helper_expr(callee))
		return instantiate_lambda_helper_call(callee.binding, args, converted);
	if (callee.binding != NULL &&
	    callee.binding->kind == BindingKind::Function)
	{
		converted = args;
		return callee.binding;
	}
	return NULL;
}

Expr Parser::finish_bound_call_expr(const Expr& callee,
                                    Binding* direct,
                                    const vector<Expr>& converted)
	{
		if (deleted_functions_.find(direct) != deleted_functions_.end())
			throw runtime_error("call to deleted function");
		bool defer_hosted_body = defer_hosted_function_body(direct);
	if (unevaluated_expression_depth_ == 0 && !defer_hosted_body)
	{
		parse_pending_function_body(direct);
		parse_pending_member_body(direct);
	}
	Expr out;
	out.type = direct->type->base;
	if (hosted_compatibility_ &&
		    direct->name == "forward_as_tuple" &&
		    direct->owner != NULL &&
		    direct->owner->kind == ScopeKind::Namespace &&
		    direct->owner->name == "std" &&
		    type_structurally_dependent(out.type))
	{
		map<Binding*, vector<TemplateArgument> >::const_iterator found_args =
			function_template_specialization_arguments_.find(direct);
		if (found_args != function_template_specialization_arguments_.end() &&
		    found_args->second.size() == 1 &&
		    found_args->second[0].kind == TemplateArgumentKind::Pack)
			{
				vector<TemplateArgument> tuple_args;
				const vector<TemplateArgument>& pack = found_args->second[0].pack;
				bool concrete_tuple_args = true;
				for (size_t i = 0; i < pack.size(); ++i)
				{
					if (pack[i].kind != TemplateArgumentKind::Type)
						break;
					TypePtr elem = pack[i].type;
					TypePtr bare = elem.get() != NULL
						? pa11::strip_cv(elem) : TypePtr();
					TypePtr ref =
						bare.get() != NULL &&
						bare->kind == pa11::TypeKind::LValueReference
						? elem : pa11::make_rvalue_reference(elem);
					if (type_structurally_dependent(ref))
						concrete_tuple_args = false;
					tuple_args.push_back(TemplateArgument::type_arg(ref));
				}
				if (concrete_tuple_args &&
				    tuple_args.size() == pack.size())
				{
					TemplateDeclaration* tuple_template =
						find_class_template(direct->owner, "tuple");
					if (tuple_template != NULL)
						out.type = instantiate_class_template(tuple_template,
						                                      tuple_args);
				}
			}
		}
	if (hosted_compatibility_ &&
	    direct->name == "forward_as_tuple" &&
	    direct->owner != NULL &&
	    direct->owner->kind == ScopeKind::Namespace &&
	    direct->owner->name == "std")
		complete_hosted_reference_tuple_layout(out.type, converted.size());
	out.category = call_category(out.type);
	out.node = Node("call-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type));
		out.node.direct_call = direct;
	out.node.suppress_virtual_dispatch = callee.node.suppress_virtual_dispatch;
	bool member_call =
		callee.node.line.compare(0, 17, "member-expression") == 0 ||
		(callee.node.has_op &&
		 (callee.node.op == OP_DOT || callee.node.op == OP_ARROW));
	out.node.virtual_dispatch =
		member_call && direct->is_virtual && !callee.node.suppress_virtual_dispatch;
	Node callee_node("callee " + qualified_decl_name(direct) +
	                 " " + pa11::describe_type(direct->type));
	callee_node.binding = direct;
	callee_node.direct_call = direct;
	add_child(out.node, callee_node);
	for (size_t i = 0; i < converted.size(); ++i)
		add_child(out.node, converted[i].node);
	bool hosted_forward_as_tuple_result =
		hosted_compatibility_ &&
		direct->name == "forward_as_tuple" &&
		direct->owner != NULL &&
		direct->owner->kind == ScopeKind::Namespace &&
		direct->owner->name == "std";
	if (unevaluated_expression_depth_ == 0 &&
	    !hosted_forward_as_tuple_result &&
	    out.category == ValueCategory::PRValue &&
	    pa11::strip_cv(out.type)->kind == pa11::TypeKind::Record &&
	    !type_is_template_dependent(out.type))
		ensure_default_destructor(out.type);
	out.valid = true;
	vector<Node> constexpr_args;
	for (size_t i = 0; i < converted.size(); ++i)
		constexpr_args.push_back(converted[i].node);
	ConstexprValue constexpr_value;
	if (unevaluated_expression_depth_ == 0 &&
	    try_evaluate_constexpr_call(direct, constexpr_args, constexpr_value))
		apply_constexpr_value(out, constexpr_value);
	annotate_expr_node(out);
	return out;
}

Expr Parser::finish_indirect_call_expr(const Expr& callee,
                                       const vector<Expr>& args,
                                       vector<Expr>& converted)
{
	TypePtr callee_type = expression_object_type(callee.type);
	callee_type = pa11::strip_cv(callee_type);
	if (callee_type->kind == pa11::TypeKind::Pointer)
		callee_type = callee_type->base;
	if (callee_type->kind != pa11::TypeKind::Function)
	{
		if (!callee.dependent_value_name.empty() ||
		    type_is_template_dependent(callee.type))
			return make_dependent_call_expr(callee, args);
		throw runtime_error("called object is not callable");
	}
	if (args.size() != callee_type->parameters.size() && !callee_type->variadic)
		throw runtime_error("wrong argument count");
	converted = args;
	for (size_t i = 0; i < callee_type->parameters.size(); ++i)
	{
		Conversion conv = convert_to(args[i], callee_type->parameters[i]);
		if (!conv.viable)
			throw runtime_error("invalid argument conversion");
		converted[i] = conv.expr;
	}
	Expr out;
	out.type = callee_type->base;
	out.category = call_category(out.type);
	out.node = Node("call-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type));
	add_child(out.node, callee.node);
	for (size_t i = 0; i < converted.size(); ++i)
		add_child(out.node, converted[i].node);
	if (unevaluated_expression_depth_ == 0 &&
	    out.category == ValueCategory::PRValue &&
	    pa11::strip_cv(out.type)->kind == pa11::TypeKind::Record &&
	    !type_is_template_dependent(out.type))
		ensure_default_destructor(out.type);
	out.valid = true;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_call_expr(Expr callee, vector<Expr> args)
{
	Expr out;
	if (make_call_pack_expr(callee, args, out) ||
	    make_member_pointer_call_expr(callee, args, out) ||
	    make_record_callable_call_expr(callee, args, out) ||
	    make_simple_builtin_call_expr(callee, args, out) ||
	    make_direct_hosted_builtin_call_expr(callee, args, out) ||
	    make_bit_count_builtin_call_expr(callee, args, out) ||
	    make_atomic_builtin_call_expr(callee, args, out) ||
	    make_bswap_builtin_call_expr(callee, args, out))
		return out;
	if (callee.binding != NULL &&
	    (callee.binding->name == "__builtin_va_start" ||
	     callee.binding->name == "__builtin_va_end"))
	{
		bool is_start = callee.binding->name == "__builtin_va_start";
		if ((is_start && args.size() < 2) || (!is_start && args.size() != 1))
			throw runtime_error("wrong argument count");
		if (!args.empty() && args[0].category != ValueCategory::LValue)
			throw runtime_error("va_list argument must be lvalue");
		out = make_direct_builtin_call(callee.binding,
		                               pa11::make_fundamental(FT_VOID),
		                               args);
		return out;
	}
	if (!callee.overloads.empty() &&
	    callee.node.line.compare(0, 17, "member-expression") == 0 &&
	    !callee.node.children.empty())
		prepare_member_call(callee, args);
	else if (!callee.overloads.empty() &&
	         callee.node.line.compare(0, 13, "id-expression") == 0)
		filter_static_class_member_overloads(callee);
	normalize_explicit_template_call_arguments(callee);
	bool dependent_template_call = call_is_dependent_template_call(callee, args);
	materialize_template_lambda_arguments(callee, args);
	if (dependent_template_call && !callee.overloads.empty())
		return make_dependent_call_expr(callee, args);
	vector<Expr> converted;
	Binding* direct = resolve_call_direct_binding(callee, args, converted);
	if (direct != NULL)
		return finish_bound_call_expr(callee, direct, converted);
	return finish_indirect_call_expr(callee, args, converted);
}

}  // namespace internal
}  // namespace pa12
