#include "pa29_toolchain.h"

#include "lowir2cy86.h"
#include "lowir2native.h"
#include "pa14_lowir.h"
#include "pa31_host_object.h"

#include <cstdio>
#include <fstream>
#include <map>
#include <stdexcept>
#include <string>
#include <unistd.h>
#include <vector>

using namespace std;

namespace pa29 {
namespace {

bool ends_with(const string& value, const string& suffix)
{
	return value.size() >= suffix.size() &&
	       value.compare(value.size() - suffix.size(), suffix.size(), suffix) == 0;
}

string normalize_target(const string& target)
{
	if (target.empty() || target == "linux")
		return target;
	if (target == "x86_64-unknown-linux-gnu" ||
	    target == "x86_64-linux-gnu")
		return "linux";
	throw runtime_error("unsupported target");
}

string object_prefix(size_t index)
{
	return "@__pa29_obj" + to_string(index) + "__";
}

bool metadata_is(const lowir2cy86::Metadata& metadata,
                 const string& key,
                 const string& value)
{
	return lowir2cy86::metadata_value(metadata, key) == value;
}

bool has_weak_binding(const lowir2cy86::Metadata& metadata)
{
	return metadata_is(metadata, "binding", "weak");
}

bool has_strong_binding(const lowir2cy86::Metadata& metadata)
{
	const string binding = lowir2cy86::metadata_value(metadata, "binding");
	return binding.empty() || binding == "strong";
}

bool has_internal_binding(const lowir2cy86::Metadata& metadata)
{
	return metadata_is(metadata, "binding", "internal");
}

void remove_metadata_key(lowir2cy86::Metadata& metadata, const string& key)
{
	lowir2cy86::Metadata kept;
	for (size_t i = 0; i < metadata.size(); ++i)
	{
		if (metadata[i].key != key)
			kept.push_back(metadata[i]);
	}
	metadata.swap(kept);
}

lowir2cy86::MetadataItem metadata_item(const string& key, const string& value)
{
	lowir2cy86::MetadataItem item;
	item.key = key;
	item.value = value;
	return item;
}

string prefixed_symbol(size_t object_index, const string& symbol)
{
	return object_prefix(object_index) + lowir2cy86::lowir_symbol_body(symbol);
}

void update_symbol(string& symbol, const map<string, string>& renames)
{
	map<string, string>::const_iterator found = renames.find(symbol);
	if (found != renames.end())
		symbol = found->second;
}

void update_metadata_symbols(lowir2cy86::Metadata& metadata,
                             const map<string, string>& renames)
{
	for (size_t i = 0; i < metadata.size(); ++i)
	{
		if (!metadata[i].global_value)
			continue;
		update_symbol(metadata[i].value, renames);
	}
}

void update_value(lowir2cy86::Value& value, const map<string, string>& renames)
{
	if (value.kind == lowir2cy86::ValueKind::Global ||
	    value.kind == lowir2cy86::ValueKind::Function)
		update_symbol(value.text, renames);
}

void update_instruction(lowir2cy86::Instruction& ins,
                        const map<string, string>& renames)
{
	update_value(ins.a, renames);
	update_value(ins.b, renames);
	update_value(ins.c, renames);
	for (size_t i = 0; i < ins.args.size(); ++i)
		update_value(ins.args[i], renames);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		update_value(ins.switch_cases[i].value, renames);
}

void update_function_references(lowir2cy86::Function& fn,
                                const map<string, string>& renames)
{
	update_metadata_symbols(fn.metadata, renames);
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			update_instruction(fn.blocks[b].instructions[i], renames);
}

void update_global_references(lowir2cy86::Global& global,
                              const map<string, string>& renames)
{
	update_metadata_symbols(global.metadata, renames);
	update_symbol(global.init.target, renames);
	for (size_t i = 0; i < global.data.size(); ++i)
		update_symbol(global.data[i].target, renames);
}

void rename_object_local_symbols(lowir2cy86::Program& program,
                                 size_t object_index,
                                 vector<string>& init_functions,
                                 vector<string>& fini_functions)
{
	map<string, string> renames;
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		if (has_internal_binding(program.globals[i].metadata))
			renames[program.globals[i].name] =
			    prefixed_symbol(object_index, program.globals[i].name);
	}
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		const string role = lowir2cy86::metadata_value(program.functions[i].metadata, "role");
		if (has_internal_binding(program.functions[i].metadata) ||
		    role == "init" ||
		    role == "fini" ||
		    program.functions[i].name == "@__cppgm_init" ||
		    program.functions[i].name == "@__cppgm_fini")
			renames[program.functions[i].name] =
			    prefixed_symbol(object_index, program.functions[i].name);
	}

	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		update_symbol(program.globals[i].name, renames);
		update_global_references(program.globals[i], renames);
	}
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		update_symbol(program.functions[i].name, renames);
		update_function_references(program.functions[i], renames);
		const string role = lowir2cy86::metadata_value(program.functions[i].metadata, "role");
		if (role == "init")
		{
			init_functions.push_back(program.functions[i].name);
			remove_metadata_key(program.functions[i].metadata, "role");
		}
		else if (role == "fini")
		{
			fini_functions.push_back(program.functions[i].name);
			remove_metadata_key(program.functions[i].metadata, "role");
		}
	}
	for (size_t i = 0; i < program.aliases.size(); ++i)
	{
		update_symbol(program.aliases[i].object, renames);
		update_symbol(program.aliases[i].target, renames);
	}
}

bool incoming_replaces_existing(const lowir2cy86::Function& existing,
                                const lowir2cy86::Function& incoming)
{
	if (existing.declaration && !incoming.declaration)
		return true;
	if (!existing.declaration && incoming.declaration)
		return false;
	if (existing.declaration && incoming.declaration)
		return false;
	if (has_weak_binding(existing.metadata) && has_strong_binding(incoming.metadata))
		return true;
	return false;
}

bool incoming_replaces_existing(const lowir2cy86::Global& existing,
                                const lowir2cy86::Global& incoming)
{
	if (existing.declaration && !incoming.declaration)
		return true;
	if (!existing.declaration && incoming.declaration)
		return false;
	if (existing.declaration && incoming.declaration)
		return false;
	if (has_weak_binding(existing.metadata) && has_strong_binding(incoming.metadata))
		return true;
	return false;
}

bool duplicate_is_allowed(const lowir2cy86::Function& existing,
                          const lowir2cy86::Function& incoming)
{
	if (existing.declaration || incoming.declaration)
		return true;
	return has_weak_binding(existing.metadata) || has_weak_binding(incoming.metadata);
}

bool duplicate_is_allowed(const lowir2cy86::Global& existing,
                          const lowir2cy86::Global& incoming)
{
	if (existing.declaration || incoming.declaration)
		return true;
	return has_weak_binding(existing.metadata) || has_weak_binding(incoming.metadata);
}

void merge_global(lowir2cy86::Program& out,
                  map<string, size_t>& names,
                  const lowir2cy86::Global& global)
{
	map<string, size_t>::iterator found = names.find(global.name);
	if (found == names.end())
	{
		names[global.name] = out.globals.size();
		out.globals.push_back(global);
		return;
	}
	lowir2cy86::Global& existing = out.globals[found->second];
	if (!duplicate_is_allowed(existing, global))
		throw runtime_error("duplicate global definition");
	if (incoming_replaces_existing(existing, global))
		existing = global;
}

void merge_function(lowir2cy86::Program& out,
                    map<string, size_t>& names,
                    const lowir2cy86::Function& fn)
{
	map<string, size_t>::iterator found = names.find(fn.name);
	if (found == names.end())
	{
		names[fn.name] = out.functions.size();
		out.functions.push_back(fn);
		return;
	}
	lowir2cy86::Function& existing = out.functions[found->second];
	if (!duplicate_is_allowed(existing, fn))
		throw runtime_error("duplicate function definition");
	if (incoming_replaces_existing(existing, fn))
		existing = fn;
}

void append_alias(lowir2cy86::Program& out,
                  map<string, string>& aliases,
                  const lowir2cy86::ObjectAlias& alias)
{
	map<string, string>::iterator found = aliases.find(alias.object);
	if (found == aliases.end())
	{
		aliases[alias.object] = alias.target;
		out.aliases.push_back(alias);
		return;
	}
	if (found->second != alias.target)
		throw runtime_error("duplicate object alias");
}

lowir2cy86::Instruction make_call_instruction(const string& callee)
{
	lowir2cy86::Instruction ins;
	ins.kind = lowir2cy86::InstrKind::Call;
	ins.type = lowir2cy86::parse_type_text("void");
	ins.a.kind = lowir2cy86::ValueKind::Function;
	ins.a.text = callee;
	return ins;
}

lowir2cy86::Instruction make_return_void_instruction()
{
	lowir2cy86::Instruction ins;
	ins.kind = lowir2cy86::InstrKind::Return;
	ins.type = lowir2cy86::parse_type_text("void");
	return ins;
}

void append_lifecycle_function(lowir2cy86::Program& out,
                               const vector<string>& callees,
                               const string& name,
                               const string& role)
{
	if (callees.empty())
		return;
	lowir2cy86::Function fn;
	fn.name = name;
	fn.ret = lowir2cy86::parse_type_text("void");
	fn.metadata.push_back(metadata_item("role", role));
	fn.metadata.push_back(metadata_item("binding", "internal"));
	lowir2cy86::Block block;
	block.name = "^entry";
	for (size_t i = 0; i < callees.size(); ++i)
		block.instructions.push_back(make_call_instruction(callees[i]));
	block.instructions.push_back(make_return_void_instruction());
	fn.blocks.push_back(block);
	out.functions.push_back(fn);
}

lowir2cy86::Program merge_objects(const vector<string>& lowir_objects)
{
	lowir2cy86::Program out;
	map<string, size_t> globals;
	map<string, size_t> functions;
	map<string, string> aliases;
	vector<string> init_functions;
	vector<string> fini_functions;
	for (size_t i = 0; i < lowir_objects.size(); ++i)
	{
		lowir2cy86::Program unit =
		    lowir2cy86::parse_files(vector<string>(1, lowir_objects[i]));
		rename_object_local_symbols(unit, i, init_functions, fini_functions);
		for (size_t g = 0; g < unit.globals.size(); ++g)
			merge_global(out, globals, unit.globals[g]);
		for (size_t f = 0; f < unit.functions.size(); ++f)
			merge_function(out, functions, unit.functions[f]);
		for (size_t a = 0; a < unit.aliases.size(); ++a)
			append_alias(out, aliases, unit.aliases[a]);
	}
	append_lifecycle_function(out, init_functions, "@__pa29_link_init", "init");
	append_lifecycle_function(out, fini_functions, "@__pa29_link_fini", "fini");
	return out;
}

struct TempFiles
{
	vector<string> paths;
	~TempFiles()
	{
		for (size_t i = 0; i < paths.size(); ++i)
			remove(paths[i].c_str());
	}
};

string temp_object_path(const string& outfile, size_t index)
{
	return outfile + ".pa29." + to_string(static_cast<long long>(getpid())) +
	       "." + to_string(index) + ".obj.tmp";
}

void compile_source_to_lowir(const string& srcfile,
                             const string& objfile,
                             const Options& options)
{
	pa14::Options lowir_options;
	lowir_options.preprocess = options.preprocess;
	lowir_options.native_lowering = true;
	pa14::emit_lowir(vector<string>(1, srcfile), objfile, lowir_options);
}

bool file_exists(const string& path)
{
	ifstream in(path.c_str(), ios::binary);
	return static_cast<bool>(in);
}

string join_path(const string& dir, const string& file)
{
	if (dir.empty() || dir == ".")
		return file;
	if (dir[dir.size() - 1] == '/')
		return dir + file;
	return dir + "/" + file;
}

vector<string> resolve_libraries(const Options& options)
{
	vector<string> objects;
	vector<string> search = options.library_paths;
	search.push_back(".");
	for (size_t i = 0; i < options.libraries.size(); ++i)
	{
		const string filename = "lib" + options.libraries[i] + ".o";
		string found;
		for (size_t p = 0; p < search.size(); ++p)
		{
			const string candidate = join_path(search[p], filename);
			if (file_exists(candidate))
			{
				found = candidate;
				break;
			}
		}
		if (found.empty())
			throw runtime_error("library not found");
		objects.push_back(found);
	}
	return objects;
}

}  // namespace

bool is_object_like_path(const string& path)
{
	return ends_with(path, ".obj") || ends_with(path, ".o");
}

void compile_source_to_object(const string& srcfile,
                              const string& objfile,
                              const Options& options)
{
	normalize_target(options.target);
	if (ends_with(objfile, ".o"))
	{
		TempFiles temps;
		const string tmp = temp_object_path(objfile, temps.paths.size());
		temps.paths.push_back(tmp);
		compile_source_to_lowir(srcfile, tmp, options);
		lowir2cy86::Program program =
		    lowir2cy86::parse_files(vector<string>(1, tmp));
		pa31::write_host_object(program, objfile);
		return;
	}
	compile_source_to_lowir(srcfile, objfile, options);
}

void link_inputs_to_executable(const vector<string>& inputs,
                               const string& outfile,
                               const Options& options)
{
	if (inputs.empty())
		throw runtime_error("no input files");
	vector<string> lowir_objects;
	TempFiles temps;
	for (size_t i = 0; i < inputs.size(); ++i)
	{
		if (is_object_like_path(inputs[i]))
		{
			lowir_objects.push_back(inputs[i]);
			continue;
		}
		const string tmp = temp_object_path(outfile, temps.paths.size());
		temps.paths.push_back(tmp);
		compile_source_to_lowir(inputs[i], tmp, options);
		lowir_objects.push_back(tmp);
	}

	vector<string> external_objects = resolve_libraries(options);

	lowir2native::Options native_options;
	native_options.target = normalize_target(options.target);
	native_options.outfile = outfile;
	native_options.external_objects = external_objects;
	lowir2native::compile_program(merge_objects(lowir_objects), native_options);
}

}  // namespace pa29
