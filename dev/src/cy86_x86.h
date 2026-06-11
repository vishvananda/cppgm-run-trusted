#pragma once

#include <vector>

#include "cy86_elf_object.h"
#include "cy86_model.h"

using namespace std;

namespace cy86 {

vector<unsigned char> build_elf_image(Program& program);
vector<unsigned char> build_elf_image(Program& program,
                                      const vector<ExternalObject>& objects);

}  // namespace cy86
