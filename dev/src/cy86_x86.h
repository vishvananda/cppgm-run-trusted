#pragma once

#include <vector>

#include "cy86_model.h"

using namespace std;

namespace cy86 {

vector<unsigned char> build_elf_image(Program& program);

}  // namespace cy86
