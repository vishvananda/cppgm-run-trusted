#include "pa11_internal.h"

#include <fstream>
#include <ostream>
#include <stdexcept>

using namespace std;

namespace pa11 {
namespace {

void indent(ostream& out, int depth)
{
	for (int i = 0; i < depth; ++i)
		out << "  ";
}

string scope_header(const Scope& scope)
{
	switch (scope.kind)
	{
	case ScopeKind::Namespace:
		return "scope namespace " +
		       (scope.parent == NULL ? string("<global>") : scope.name);
	case ScopeKind::TemplateParameters:
		return "scope template-parameters";
	case ScopeKind::Class:
		return "scope class " + scope.name;
	case ScopeKind::Enum:
		return "scope enum " + scope.name;
	case ScopeKind::Function:
		return "scope function " + scope.name;
	case ScopeKind::Block:
		return "scope block";
	}
	throw logic_error("unknown scope kind");
}

const char* binding_keyword(BindingKind kind)
{
	switch (kind)
	{
	case BindingKind::Type:
		return "type";
	case BindingKind::TypeAlias:
		return "type-alias";
	case BindingKind::Variable:
		return "variable";
	case BindingKind::Function:
		return "function";
	case BindingKind::Parameter:
		return "parameter";
	case BindingKind::Enumerator:
		return "enumerator";
	case BindingKind::Namespace:
	case BindingKind::NamespaceAlias:
		break;
	}
	throw logic_error("binding kind has no dump spelling");
}

void emit_binding(const Binding& binding, ostream& out, int depth)
{
	indent(out, depth);
	out << binding_keyword(binding.kind) << ' ' << binding.name << ' '
	    << describe_type(binding.type);
	if (binding.kind == BindingKind::Enumerator)
		out << ' ' << binding.constant_value;
	out << '\n';
}

void emit_scope(const Scope& scope, ostream& out, int depth)
{
	indent(out, depth);
	out << scope_header(scope) << '\n';
	for (size_t i = 0; i < scope.binding_order.size(); ++i)
		emit_binding(*scope.binding_order[i], out, depth + 1);
	for (size_t i = 0; i < scope.child_order.size(); ++i)
		emit_scope(*scope.child_order[i], out, depth + 1);
}

}  // namespace

void emit_translation_unit(const TranslationUnit& tu, ostream& out)
{
	out << "translation-unit\n";
	emit_scope(*tu.global_scope, out, 1);
}

void emit_types(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options)
{
	ofstream out(outfile.c_str());
	if (!out)
		throw runtime_error("cannot open output file");

	vector<TranslationUnit> units;
	for (size_t i = 0; i < srcfiles.size(); ++i)
		units.push_back(analyze_source_file(srcfiles[i], options));

	out << units.size() << " translation units\n";
	for (size_t i = 0; i < units.size(); ++i)
	{
		out << "start translation unit " << (i + 1) << '\n';
		emit_translation_unit(units[i], out);
		out << "end translation unit\n";
	}
}

}  // namespace pa11
