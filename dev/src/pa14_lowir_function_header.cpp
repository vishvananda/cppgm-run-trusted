#include "pa14_lowir_function_internal.h"
#include "pa12_templates_function_support.h"

#include <sstream>

namespace pa14 {
namespace internal {

bool FunctionLowerer::initialize_function_header(Binding* binding,
                                                 TypePtr fn_type)
{
	out_.binding = binding;
	string name = program_.symbol_for(binding);
	out_.name = name;
	bool indirect_result =
		pa11::strip_cv(fn_type->base)->kind == TypeKind::Record &&
		record_return_by_address(fn_type->base);
	ostringstream header;
	out_.returns_pointer_result =
		!indirect_result && scalar_lowir_type(fn_type->base) == "ptr";
	out_.returns_record_result =
		pa11::strip_cv(fn_type->base)->kind == TypeKind::Record;
	vector<string> raw_parameter_names;
	map<string, int> raw_parameter_counts;
	for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{
		string pname = i < fn_.children.size() &&
			starts_with(fn_.children[i].line, "parameter ")
			? fn_.children[i].line.substr(10) : "";
		size_t space = pname.find(' ');
		pname = space == string::npos ? pname : pname.substr(0, space);
		if ((pname.empty() || pname.compare(0, 7, "__param") == 0) &&
		    i < binding->function_parameter_names.size() &&
		    !binding->function_parameter_names[i].empty() &&
		    binding->function_parameter_names[i].compare(0, 7, "__param") != 0)
			pname = binding->function_parameter_names[i];
		raw_parameter_names.push_back(pname);
		if (!pname.empty())
			++raw_parameter_counts[pname];
	}
	map<string, int> parameter_name_counts;
	map<string, int> raw_parameter_seen;
	header << "function @" << name << "(";
	if (indirect_result)
	{
		header << "%ret : ptr [pass=indirect_result]";
		parameter_name_counts["ret"] = 1;
	}
	for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{
		if (i != 0 || indirect_result)
			header << ", ";
		string pname = raw_parameter_names[i];
		if (!pname.empty())
			++raw_parameter_seen[pname];
		if (pname.empty() ||
		    raw_parameter_seen[pname] < raw_parameter_counts[pname])
			pname = "__param" + to_string(i);
		int& count = parameter_name_counts[pname];
		++count;
		if (count > 1)
			pname += "__shadow" + to_string(count);
		out_.parameter_names.push_back(pname);
		header << "%" << pname << " : "
		       << lowir_parameter(fn_type->parameters[i]);
	}
	size_t hidden_pvb_index = 0;
	bool member_this_param =
		fn_.binding->owner != NULL &&
		fn_.binding->owner->kind == ScopeKind::Class &&
		!fn_.binding->is_static_member &&
		!fn_type->parameters.empty();
	for (size_t i = member_this_param ? 1 : 0;
	     i < fn_type->parameters.size();
	     ++i)
	{
		vector<TypePtr> vbases =
			program_.hidden_virtual_bases_for_function_parameter(
				fn_.binding, i, fn_type->parameters[i]);
		for (size_t v = 0; v < vbases.size(); ++v)
		{
			if (hidden_pvb_index != 0 ||
			    !fn_type->parameters.empty() ||
			    indirect_result)
				header << ", ";
			header << "%__pvbptr" << hidden_pvb_index++ << " : ptr";
		}
	}
	vector<TypePtr> this_vbases =
		member_this_param &&
		!is_class_constructor_binding(fn_.binding) &&
		!is_class_destructor_binding(fn_.binding)
		? (fn_.binding->is_virtual
		   ? program_.hidden_virtual_bases_for_function_parameter(
			   fn_.binding, 0, fn_type->parameters[0])
		   : hidden_virtual_bases_for_record(class_record_for_member(fn_.binding)))
		: vector<TypePtr>();
	for (size_t v = 0; v < this_vbases.size(); ++v)
	{
		if (hidden_pvb_index != 0 ||
		    !fn_type->parameters.empty() ||
		    indirect_result ||
		    v != 0)
			header << ", ";
		header << "%__vbptr" << v << " : ptr";
	}
	header << ") -> "
	       << (indirect_result ? "void" : scalar_lowir_type(fn_type->base));
	vector<string> metadata;
	if (fn_type->variadic)
		metadata.push_back("arity=variadic");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	if (binding->unwind_no)
		metadata.push_back("unwind=no");
	if (binding->name == "__cppgm_init")
		metadata.push_back("role=init"), metadata.push_back("binding=internal");
	else if (binding->name == "__cppgm_fini")
		metadata.push_back("role=fini"), metadata.push_back("binding=internal");
	else if (binding->name == "main")
		metadata.push_back("role=entry"), metadata.push_back("binding=strong"),
		out_.strong_binding = true, metadata.push_back("keep_alias=yes");
	else if (binding->name.compare(0, 8, "__lambda") == 0 ||
	         binding_has_internal_linkage(binding))
		metadata.push_back("binding=internal");
	else if (lowir_synthesizable_hosted_inline_body(binding) ||
	         binding->is_inline_definition ||
	         (binding_has_template_specialization_context(binding) &&
	          !binding->is_explicit_specialization_member))
		metadata.push_back("binding=weak");
	else
		metadata.push_back("binding=strong"), out_.strong_binding = true;
	if (binding->name != "main" &&
	    binding->name != "__cppgm_init" &&
	    binding->name != "__cppgm_fini")
	{
		string object_symbol = global_object_symbol(binding);
		if (!object_symbol.empty())
			metadata.push_back("object=" + object_symbol);
	}
	if (program_.host_object_lowering && binding->is_generated_default_constructor)
		metadata.push_back("generated_default_ctor=yes");
	if (binding->is_object_root && !binding->is_defaulted)
		metadata.push_back("object_root=yes");
	header << metadata_suffix(metadata);
	out_.header = header.str();
	return indirect_result;
}

}  // namespace internal
}  // namespace pa14
