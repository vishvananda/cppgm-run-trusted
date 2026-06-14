#include "pa12_templates_function_instantiation_engine.h"

using namespace std;

namespace pa12 {
namespace internal {

Binding* Parser::instantiate_function_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	return instantiate_function_template_with_engine(
		*this,
		declaration,
		arguments);
}

Binding* instantiate_function_template_with_engine(
	Parser& parser,
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	FunctionTemplateInstantiationEngine engine(
		parser,
		declaration,
		arguments);
	return engine.run();
}

}  // namespace internal
}  // namespace pa12
