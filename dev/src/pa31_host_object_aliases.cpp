#include "pa31_host_object_internal.h"

#include <stdexcept>

using namespace std;

namespace pa31 {
namespace host {
	bool constructor_object_symbol(const string& object);
	bool noop_constructor_instruction(const Function& fn, const Instruction& ins);

	const Symbol* find_emitted_symbol(const ObjectFile& obj, const string& name)
	{
		for (size_t i = 0; i < obj.symbols.size(); ++i)
			if (obj.symbols[i].name == name)
				return &obj.symbols[i];
		return NULL;
	}
	bool noop_constructor_body(const Function& fn)
	{
		if (fn.declaration ||
		    !constructor_object_symbol(metadata(fn.metadata, "object")) ||
		    !lowir2cy86::is_void_type(fn.ret) ||
		    fn.params.size() != 1 ||
		    !lowir2cy86::is_ptr_type(fn.params[0].type))
			return false;
		for (size_t b = 0; b < fn.blocks.size(); ++b)
			for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
				if (!noop_constructor_instruction(
					    fn, fn.blocks[b].instructions[i]))
					return false;
		return true;
	}
	bool Unit::aliases_noop_constructor_to_complete_entry(
		const Function& fn) const
	{
		if (!noop_constructor_body(fn))
			return false;
		const string object = metadata(fn.metadata, "object");
		if (object.find("C2") == string::npos)
			return false;
		for (size_t i = 0; i < program.aliases.size(); ++i)
		{
			if (program.aliases[i].object != object ||
			    program.aliases[i].target == fn.name ||
			    prunes_function(program.aliases[i].target))
				continue;
			map<string, size_t>::const_iterator target =
				program.function_by_name.find(program.aliases[i].target);
			if (target == program.function_by_name.end())
				continue;
			const Function& target_fn = program.functions[target->second];
			const string target_object =
				metadata(target_fn.metadata, "object");
			if (target_object.find("C1") != string::npos &&
			    noop_constructor_body(target_fn))
				return true;
		}
		return false;
	}
	void Unit::emit_aliases()
	{
		for (size_t i = 0; i < program.aliases.size(); ++i)
		{
			const string target = target_symbol(program, program.aliases[i].target);
			const Symbol* sym = find_emitted_symbol(obj, target);
			if ((sym == NULL || !sym->defined) &&
			    prunes_function(program.aliases[i].target))
				continue;
			if (sym == NULL || !sym->defined)
				throw runtime_error("object alias target not defined");
			obj.symbol(program.aliases[i].object,
			           sym->bind,
			           sym->type,
			           sym->section,
			           sym->value,
			           sym->size);
		}
	}
}  // namespace host
}  // namespace pa31
