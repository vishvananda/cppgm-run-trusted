#pragma once

#include "lowir2cy86.h"

#include <cstddef>
#include <string>

namespace lowir2cy86 {

std::string native_cy86_literal(const Type& type,
                                const std::string& literal,
                                bool native_output);
std::size_t native_global_alignment(const Global& global);

}  // namespace lowir2cy86
