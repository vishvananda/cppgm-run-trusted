#include "pa12_expr_semantics_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

struct CallArgumentConverter
{
	Parser& p;
	Binding* fn;
	const vector<Expr>& args;
	vector<Expr>& conv_args;
	vector<int>& ranks;
	int& object_rank;
	map<pair<size_t, const void*>, Conversion>& conversion_cache;

	CallArgumentConverter(Parser& parser,
	                      Binding* binding,
	                      const vector<Expr>& call_args,
	                      vector<Expr>& converted,
	                      vector<int>& rank_out,
	                      int& object_rank_out,
	                      map<pair<size_t, const void*>, Conversion>& cache)
	  : p(parser), fn(binding), args(call_args), conv_args(converted),
	    ranks(rank_out), object_rank(object_rank_out),
	    conversion_cache(cache)
	{
	}

	void append_default_arguments()
	{
		if (conv_args.size() >= fn->type->parameters.size())
			return;
		const vector<Expr>& defaults = p.default_arguments_[fn];
		for (size_t j = conv_args.size(); j < fn->type->parameters.size(); ++j)
		{
			Expr default_arg = defaults[j];
			if (default_arg.valid &&
			    p.type_is_template_dependent(default_arg.type) &&
			    !p.type_is_template_dependent(fn->type->parameters[j]))
			{
				Expr instantiated;
				if (p.instantiate_function_default_argument(
					    fn, default_arg, fn->type->parameters[j],
					    instantiated))
					default_arg = instantiated;
				else
				{
					default_arg.type = fn->type->parameters[j];
					annotate_expr_node(default_arg);
				}
			}
			conv_args.push_back(default_arg);
		}
	}

	bool implicit_object_argument(size_t index) const
	{
		return index == 0 &&
		       fn->owner != NULL &&
		       fn->owner->kind == ScopeKind::Class &&
		       !fn->is_static_member;
	}

	static unsigned cv_flags(TypePtr type)
	{
		return type.get() != NULL && type->kind == pa11::TypeKind::Cv
			? type->cv : pa11::CV_NONE;
	}

	bool related_object_parameter(TypePtr source,
	                              TypePtr target,
	                              TypePtr& source_record,
	                              TypePtr& target_record) const
	{
		source_record = pa11::strip_cv(source->base);
		target_record = pa11::strip_cv(target->base);
		bool related =
			call_object_specialization_type_equivalent(source->base,
			                                           target->base);
		if (!related &&
		    source_record.get() != NULL &&
		    target_record.get() != NULL &&
		    source_record->kind == pa11::TypeKind::Record &&
		    target_record->kind == pa11::TypeKind::Record)
			related = p.record_base_distance(source_record, target_record) <
				1000000;
		return related;
	}

	unsigned active_this_cv(TypePtr source_record, unsigned fallback) const
	{
		for (size_t ai = p.active_functions_.size(); ai > 0; --ai)
		{
			Binding* active = p.active_functions_[ai - 1];
			if (active == NULL ||
			    active->type.get() == NULL ||
			    active->type->kind != pa11::TypeKind::Function ||
			    active->type->parameters.empty())
				continue;
			TypePtr active_this = pa11::strip_cv(active->type->parameters[0]);
			if (active_this.get() == NULL ||
			    active_this->kind != pa11::TypeKind::Pointer ||
			    active_this->base.get() == NULL)
				continue;
			TypePtr active_record = pa11::strip_cv(active_this->base);
			if (active_record.get() == NULL ||
			    source_record.get() == NULL ||
			    active_record->kind != pa11::TypeKind::Record ||
			    source_record->kind != pa11::TypeKind::Record ||
			    active_record->scope != source_record->scope)
				continue;
			return cv_flags(active_this->base);
		}
		return fallback;
	}

	bool check_implicit_object_cv(size_t index) const
	{
		TypePtr source = pa11::strip_cv(
			p.lvalue_to_rvalue_type(conv_args[index].type));
		TypePtr target = pa11::strip_cv(fn->type->parameters[index]);
		if (source.get() == NULL ||
		    target.get() == NULL ||
		    source->kind != pa11::TypeKind::Pointer ||
		    target->kind != pa11::TypeKind::Pointer ||
		    source->base.get() == NULL ||
		    target->base.get() == NULL)
			return true;
		TypePtr source_record;
		TypePtr target_record;
		if (!related_object_parameter(source, target, source_record, target_record))
			return true;
		unsigned source_cv = cv_flags(source->base);
		if (source_cv == pa11::CV_NONE &&
		    conv_args[index].binding != NULL &&
		    conv_args[index].binding->name == "this")
			source_cv = active_this_cv(source_record, source_cv);
		unsigned target_cv = cv_flags(target->base);
		return (target_cv & source_cv) == source_cv;
	}

	bool apply_exact_object_fallback(size_t index,
	                                 Conversion& conv,
	                                 bool& conversion_failed) const
	{
		bool constructor_object_arg =
			fn->owner != NULL &&
			fn->owner->kind == ScopeKind::Class &&
			fn->name == fn->owner->name;
		TypePtr source = pa11::strip_cv(
			p.lvalue_to_rvalue_type(conv_args[index].type));
		TypePtr target = pa11::strip_cv(fn->type->parameters[index]);
		if (constructor_object_arg ||
		    source.get() == NULL ||
		    target.get() == NULL ||
		    source->kind != pa11::TypeKind::Pointer ||
		    target->kind != pa11::TypeKind::Pointer ||
		    source->base.get() == NULL ||
		    target->base.get() == NULL ||
		    !call_object_specialization_type_equivalent(source->base,
		                                                target->base))
			return true;
		unsigned source_cv = cv_flags(source->base);
		unsigned target_cv = cv_flags(target->base);
		if ((target_cv & source_cv) != source_cv)
			return false;
		unsigned added_cv = target_cv & ~source_cv;
		int rank = 0;
		if ((added_cv & pa11::CV_CONST) != 0)
			++rank;
		if ((added_cv & pa11::CV_VOLATILE) != 0)
			++rank;
		Expr converted = conv_args[index];
		converted.type = fn->type->parameters[index];
		converted.category = ValueCategory::PRValue;
		converted.node = Node("cast-expression prvalue " +
		                      pa11::describe_type(converted.type));
		add_child(converted.node, conv_args[index].node);
		annotate_expr_node(converted);
		conv = Conversion(true, rank, converted);
		conversion_failed = false;
		return true;
	}

	bool convert_argument(size_t index)
	{
		bool implicit = implicit_object_argument(index);
		if (implicit && !check_implicit_object_cv(index))
			return false;
		Conversion conv;
		bool conversion_failed = false;
		bool cacheable = !implicit && index < args.size();
		pair<size_t, const void*> cache_key =
			make_pair(index, fn->type->parameters[index].get());
		map<pair<size_t, const void*>, Conversion>::iterator cached =
			cacheable ? conversion_cache.find(cache_key)
			: conversion_cache.end();
		if (cached != conversion_cache.end())
			conv = cached->second;
		else
		{
			try
			{
				conv = p.convert_to(conv_args[index], fn->type->parameters[index]);
			}
			catch (const runtime_error&)
			{
				conversion_failed = true;
			}
			if (cacheable)
				conversion_cache[cache_key] = conversion_failed
					? Conversion() : conv;
		}
		if ((conversion_failed || !conv.viable) && implicit &&
		    !apply_exact_object_fallback(index, conv, conversion_failed))
			return false;
		if (conversion_failed || !conv.viable)
			return false;
		bool supplied_arg = index < args.size();
		if (implicit)
			object_rank = conv.rank;
		else if (supplied_arg)
			ranks.push_back(conv.rank);
		conv_args[index] = conv.expr;
		return true;
	}

	bool convert()
	{
		conv_args = args;
		append_default_arguments();
		object_rank = -1;
		for (size_t j = 0; j < fn->type->parameters.size(); ++j)
			if (!convert_argument(j))
				return false;
		return true;
	}
};

bool Parser::convert_call_candidate_arguments(Binding* fn,
                                              const vector<Expr>& args,
                                              vector<Expr>& conv_args,
                                              vector<int>& ranks,
                                              int& object_rank,
                                              map<pair<size_t, const void*>,
                                                  Conversion>& conversion_cache)
{
	CallArgumentConverter converter(*this, fn, args, conv_args, ranks,
	                                object_rank, conversion_cache);
	return converter.convert();
}

}  // namespace internal
}  // namespace pa12
