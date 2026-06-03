#include "nsdecl_support.h"

#include <ostream>

#include "nsdecl_internal.h"

using namespace std;

namespace nsdecl {

void describe_translation_units(const vector<string>& srcfiles,
                                const Options& options,
                                ostream& out)
{
	out << srcfiles.size() << " translation units\n";
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		TranslationUnit tu = parse_source_file(srcfiles[i], options);
		emit_translation_unit(tu, out);
	}
}

}  // namespace nsdecl
