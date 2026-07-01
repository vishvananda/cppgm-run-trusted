#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {
namespace {

bool hosted_std_namespace_scope(const Scope* scope)
{
	for (const Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

bool hosted_make_shared_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == "make_shared" &&
	       binding->owner != NULL &&
	       hosted_std_namespace_scope(binding->owner);
}

bool hosted_shared_ptr_element(TypePtr type, TypePtr& element)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (!hosted_shared_ptr_record(bare) ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	element = bare->template_arguments[0].type;
	return element.get() != NULL;
}

bool known_heap_factory_object(const Node& expr, TypePtr& object)
{
	if (!starts_with(expr.line, "call-expression") ||
	    !hosted_make_shared_binding(expr.direct_call) ||
	    !hosted_shared_ptr_element(expr.type, object))
		return false;
	object = pa11::strip_cv(object);
	return object.get() != NULL;
}

TypePtr normalized_value_type(TypePtr type)
{
	return type.get() != NULL ? pa11::strip_cv(strip_for_value(type)) :
		TypePtr();
}

bool same_unqualified_type(TypePtr left, TypePtr right)
{
	return left.get() != NULL &&
	       right.get() != NULL &&
	       pa11::same_type(pa11::strip_cv(left), pa11::strip_cv(right));
}

string unqualified_template_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool hosted_basic_string_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL ||
	    unqualified_template_primary_name(bare) != "basic_string")
		return false;
	return hosted_std_namespace_scope(bare->scope);
}

bool hosted_vector_bool_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL ||
	    unqualified_template_primary_name(bare) != "vector" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(bare->template_arguments[0].type);
	return element.get() != NULL &&
	       element->kind == TypeKind::Fundamental &&
	       element->fundamental == FT_BOOL &&
	       hosted_std_namespace_scope(bare->scope);
}

bool hosted_vector_bool_insert_aux_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == pa11::abi_private_name("M_insert_aux") &&
	       hosted_vector_bool_record(class_record_for_member(binding));
}

bool literal_char_pointer_argument(const Node& arg)
{
	return !arg.token_text.empty() &&
	       arg.token_text[arg.token_text.size() - 1] == '"';
}

bool char_pointer_value_type(TypePtr type)
{
	TypePtr value = normalized_value_type(type);
	TypePtr pointee = value.get() != NULL &&
	                  value->kind == TypeKind::Pointer
		? pa11::strip_cv(value->base) : TypePtr();
	return pointee.get() != NULL &&
	       pointee->kind == TypeKind::Fundamental &&
	       pointee->fundamental == FT_CHAR;
}

bool char_pointer_argument(const Node& arg)
{
	if (literal_char_pointer_argument(arg))
		return true;
	return char_pointer_value_type(substituted_expression_type(arg));
}

Binding* find_basic_string_cstr_constructor(TypePtr type,
                                            TypePtr& allocator)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (!hosted_basic_string_record(bare) ||
	    bare->scope == NULL ||
	    bare->template_arguments.size() < 3 ||
	    bare->template_arguments[2].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return NULL;
	TypePtr alloc_arg = bare->template_arguments[2].type;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding == NULL ||
		    binding->kind != BindingKind::Function ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 3 ||
		    !char_pointer_value_type(binding->type->parameters[1]) ||
		    !is_reference(binding->type->parameters[2]))
			continue;
		TypePtr param_alloc =
			pa11::strip_cv(binding->type->parameters[2]->base);
		if (!same_unqualified_type(param_alloc, alloc_arg))
			continue;
		allocator = param_alloc;
		return canonical_constructor_binding(binding);
	}
	return NULL;
}

int constructor_parameter_score(TypePtr param, const Node& arg)
{
	TypePtr arg_type = substituted_expression_type(arg);
	TypePtr param_value =
		normalized_value_type(is_reference(param) ? param->base : param);
	TypePtr arg_value = normalized_value_type(arg_type);
	if (param_value.get() == NULL || arg_value.get() == NULL)
		return -1;
	if (same_unqualified_type(param_value, arg_value))
		return 100;
	if (param_value->kind == TypeKind::Pointer &&
	    arg_value->kind == TypeKind::Pointer &&
	    same_unqualified_type(param_value->base, arg_value->base))
		return 90;
	if (is_reference(param))
	{
		TypePtr param_object = pa11::strip_cv(param->base);
		TypePtr arg_object = pa11::strip_cv(object_type(arg_type));
		if (param_object.get() != NULL &&
		    arg_object.get() != NULL &&
		    param_object->kind == TypeKind::Record &&
		    arg_object->kind == TypeKind::Record &&
		    same_unqualified_type(param_object, arg_object))
			return 80;
		return -1;
	}
	return -1;
}

Binding* find_constructor_for_arguments(TypePtr type,
                                        const vector<const Node*>& args)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	Binding* best = NULL;
	int best_score = -1;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding == NULL ||
		    binding->kind != BindingKind::Function ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != args.size() + 1)
			continue;
		int score = 0;
		bool viable = true;
		for (size_t j = 0; j < args.size(); ++j)
		{
			int part = constructor_parameter_score(
				binding->type->parameters[j + 1], *args[j]);
			if (part < 0)
			{
				viable = false;
				break;
			}
			score += part;
		}
		if (viable && score > best_score)
		{
			best = binding;
			best_score = score;
		}
	}
	return best != NULL ? canonical_constructor_binding(best) : NULL;
}

}  // namespace

bool FunctionLowerer::lower_hosted_basic_string_cstr_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& arg)
{
	const Node* source = &arg;
	if (starts_with(arg.line, "braced-init-list") &&
	    arg.children.size() == 1 &&
	    char_pointer_argument(arg.children[0]))
		source = &arg.children[0];
	if (starts_with(arg.line, "cast-expression") &&
	    arg.children.size() == 1 &&
	    char_pointer_argument(arg.children[0]))
		source = &arg.children[0];
	if (!char_pointer_argument(*source))
		return false;
	TypePtr allocator;
	Binding* ctor = find_basic_string_cstr_constructor(type, allocator);
	if (ctor == NULL)
		return false;
	return lower_char_pointer_record_constructor_init(addr_for,
	                                                  ctor,
	                                                  allocator,
	                                                  *source);
}

bool FunctionLowerer::lower_char_pointer_record_constructor_init(
	const function<Value()>& addr_for,
	Binding* ctor,
	TypePtr allocator,
	const Node& arg)
{
	Value target = addr_for();
	string allocator_slot = fresh_aux_slot("stralloc",
	                                      slot_lowir_type(allocator));
	string allocator_addr_name = fresh_temp();
	instr(allocator_addr_name + " = addr $" + allocator_slot);
	Value allocator_addr("ptr", allocator_addr_name);
	function<Value()> allocator_addr_for = [allocator_addr]() {
		return allocator_addr;
	};
	lower_default_init(allocator_addr_for, allocator);
	vector<string> lowered;
	lowered.push_back(target.text);
	lower_call_argument(arg, ctor->type->parameters[1], lowered);
	lowered.push_back(allocator_addr.text);
	program_.demand_function_declaration(ctor);
	string callee = program_.symbol_for(ctor);
	ostringstream call;
	call << "call void @" << callee << "(";
	for (size_t i = 0; i < lowered.size(); ++i)
	{
		if (i != 0)
			call << ", ";
		call << lowered[i];
	}
	call << ")";
	instr(call.str());
	return true;
}

bool FunctionLowerer::lower_known_heap_factory_call(
	const function<Value()>& addr_for,
	const Node& expr)
{
	TypePtr object;
	if (!known_heap_factory_object(expr, object))
		return false;
	return lower_heap_object_factory_call(addr_for, expr, object);
}

bool FunctionLowerer::lower_heap_object_factory_call(
	const function<Value()>& addr_for,
	const Node& expr,
	TypePtr object)
{
	if (program_.declared_functions.insert("operator_new").second)
		program_.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	string size_tmp = fresh_temp();
	instr(size_tmp + " = convert sext i64 i32 " +
	      to_string(pa11::type_size(object)));
	string object_tmp = fresh_temp();
	instr(object_tmp + " = call ptr @operator_new(" + size_tmp + ")");
	Value object_addr("ptr", object_tmp);
	function<Value()> object_addr_for = [object_addr]() {
		return object_addr;
	};
	size_t argc = expr.children.empty() ? 0 : expr.children.size() - 1;
	if (object->kind == TypeKind::Record)
	{
		if (argc == 0)
			lower_default_init(object_addr_for, object);
		else
		{
			vector<const Node*> args;
			for (size_t i = 1; i < expr.children.size(); ++i)
				args.push_back(&expr.children[i]);
			Binding* ctor = find_constructor_for_arguments(object, args);
			if (ctor != NULL)
				lower_constructor_call(object_addr_for, ctor, args);
			else if (argc == 1)
				lower_object_init(object_addr_for, object,
				                  expr.children[1]);
			else
				throw runtime_error("no matching make_shared constructor");
		}
	}
	else
	{
		if (argc == 0)
			lower_zero_init(object_addr_for, object);
		else if (argc == 1)
			lower_scalar_object_init(object_addr_for, object,
			                         expr.children[1]);
		else
			throw runtime_error("too many make_shared scalar arguments");
	}
	Value target = addr_for();
	instr("store ptr " + object_addr.text + ", " + target.text);
	string control = fresh_temp();
	instr(control + " = index i8 [projection=field] " +
	      target.text + ", 8");
	instr("store ptr 0, " + control);
	return true;
}
}  // namespace internal
}  // namespace pa14
