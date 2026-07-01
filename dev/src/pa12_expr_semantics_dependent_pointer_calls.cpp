#include "pa12_expr_semantics_support.h"
#include "pa12_types_support.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

string call_unqualified_template_primary(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL)
		return string();
	string primary = record->template_primary_name.empty()
		? record->name : record->template_primary_name;
	size_t pos = primary.rfind("::");
	primary = pos == string::npos ? primary : primary.substr(pos + 2);
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	return primary;
}

bool call_record_has_enable_shared_from_this_base(TypePtr record,
                                                  set<const void*>& seen)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != pa11::TypeKind::Record ||
	    !seen.insert(record.get()).second)
		return false;
	vector<TypePtr> bases = pa11::record_direct_bases(record);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (call_unqualified_template_primary(base) ==
		        "enable_shared_from_this" ||
		    call_record_has_enable_shared_from_this_base(base, seen))
			return true;
	}
	return false;
}

}  // namespace

bool dependent_pointer_member_helper_candidate(Binding* fn,
                                               const vector<Expr>& args)
{
	if (fn == NULL ||
	    args.size() != 2 ||
	    fn->type.get() == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    fn->type->parameters.size() != 2 ||
	    fn->owner == NULL ||
	    fn->owner->kind != ScopeKind::Class ||
	    fn->is_static_member)
		return false;
	TypePtr self = pa11::strip_cv(fn->type->parameters[0]);
	if (self.get() == NULL ||
	    self->kind != pa11::TypeKind::Pointer)
		return false;
	TypePtr owner = pa11::strip_cv(self->base);
	TypePtr parameter = pa11::strip_cv(fn->type->parameters[1]);
	return owner.get() != NULL &&
	       owner->kind == pa11::TypeKind::Record &&
	       parameter.get() != NULL &&
	       parameter->kind == pa11::TypeKind::Pointer &&
	       type_structurally_dependent(parameter->base);
}

bool hosted_esft_argument_has_base(const vector<Expr>& args)
{
	if (args.size() < 2 || args[1].type.get() == NULL)
		return false;
	TypePtr pointer = pa11::strip_cv(args[1].type);
	if (pointer.get() == NULL || pointer->kind != pa11::TypeKind::Pointer)
		return false;
	TypePtr pointee = pa11::strip_cv(pointer->base);
	set<const void*> seen;
	return call_record_has_enable_shared_from_this_base(pointee, seen);
}

void model_dependent_pointer_member_helper_candidate(Binding* fn,
                                                     const vector<Expr>& args)
{
	if (!dependent_pointer_member_helper_candidate(fn, args))
		return;
	TypePtr param = pa11::strip_cv(fn->type->parameters[1]);
	if (param.get() == NULL ||
	    param->kind != pa11::TypeKind::Pointer ||
	    !type_structurally_dependent(param->base))
		return;
	vector<TypePtr> params = fn->type->parameters;
	params[1] = args[1].type;
	TypePtr modeled = pa11::make_function(
		pa11::make_fundamental(FT_VOID),
		params,
		false);
	modeled->cv = fn->type->cv;
	modeled->ref_qualifier = fn->type->ref_qualifier;
	fn->type = modeled;
}

}  // namespace internal
}  // namespace pa12
