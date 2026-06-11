#pragma once

#include "lowir2cy86.h"

#include <iosfwd>
#include <string>

namespace lowir2cy86 {

bool program_needs_declared_runtime_function(const Program& program,
                                             const std::string& name);
bool program_needs_allocator_runtime(const Program& program);
std::string emit_i128_runtime_cy86();
void append_required_abi_runtime_cy86(std::ostream& out,
                                      const Program& program,
                                      int& eh_label_counter);
void append_eh_runtime_cy86(std::ostream& out,
                            bool native_output,
                            int& eh_label_counter);
void append_eh_runtime_globals_cy86(std::ostream& out, bool native_output);
void append_allocator_runtime_globals_cy86(std::ostream& out);
void append_external_rtti_vtable_stubs_cy86(std::ostream& out,
                                            const Program& program);

}  // namespace lowir2cy86
