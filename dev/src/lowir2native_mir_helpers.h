#pragma once

#include "lowir2cy86.h"
#include "lowir2native.h"

#include <cstddef>
#include <iosfwd>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace lowir2native {

std::string effective_target(const Options& options);
void write_text_file(const std::string& path, const std::string& text);
void dump_mir_startup(std::ostream& out, const lowir2cy86::Program& program);
void dump_mir_globals(std::ostream& out, const lowir2cy86::Program& program);
void dump_mir_abi(std::ostream& out, const lowir2cy86::Function& fn);
void dump_mir_frame(std::ostream& out, const lowir2cy86::Program& program,
                    const lowir2cy86::Function& fn,
                    const std::vector<std::string>& preserves,
                    const std::set<std::string>& omitted_slots);
void analyze_mir_promoted_slots(
    const lowir2cy86::Function& fn,
    std::map<std::string, std::string>& promoted_slot_params,
    std::map<std::string, std::string>& promoted_loads,
    std::set<std::string>& omitted_slots);
void analyze_mir_frame_temps(const lowir2cy86::Program& program,
                             const lowir2cy86::Function& fn,
                             std::set<std::string>& frame_temps);
void dump_mir_frame_temps(std::ostream& out,
                          const lowir2cy86::Function& fn,
                          const std::set<std::string>& frame_temps,
                          const std::set<std::string>& omitted_slots);
void dump_mir_f80_param_saves(std::ostream& out,
                              const lowir2cy86::Function& fn);
bool mir_call_has_f80_arg(const lowir2cy86::Function& fn,
                          const lowir2cy86::Instruction& ins);
void dump_mir_f80_call(std::ostream& out,
                       const lowir2cy86::Function& fn,
                       const lowir2cy86::Instruction& ins,
                       const std::set<std::string>& omitted_slots);
bool mir_call_arg_needs_address(const lowir2cy86::Program& program,
                                const lowir2cy86::Instruction& ins,
                                std::size_t index);
bool mir_is_xmm_type(const lowir2cy86::Type& type);
std::string abi_xmm(std::size_t index);
std::string mir_abi_param_location(const lowir2cy86::Function& fn,
                                   std::size_t index);
bool mir_param_needs_slot(const lowir2cy86::Function& fn,
                          std::size_t index);
lowir2cy86::Type mir_call_param_type(const lowir2cy86::Program& program,
                                     const lowir2cy86::Function& fn,
                                     const lowir2cy86::Instruction& ins,
                                     std::size_t index);
std::string mir_call_arg_register(const lowir2cy86::Program& program,
                                  const lowir2cy86::Function& fn,
                                  const lowir2cy86::Instruction& ins,
                                  std::size_t index);
std::size_t mir_call_stack_arg_offset(const lowir2cy86::Program& program,
                                      const lowir2cy86::Function& fn,
                                      const lowir2cy86::Instruction& ins,
                                      std::size_t index);
std::size_t mir_call_stack_arg_bytes(const lowir2cy86::Program& program,
                                     const lowir2cy86::Function& fn,
                                     const lowir2cy86::Instruction& ins);
bool mir_has_stack_arg_call(const lowir2cy86::Program& program,
                            const lowir2cy86::Function& fn);
std::size_t align_to(std::size_t value, std::size_t alignment);
bool mir_skip_promoted_slot_instruction(
    const lowir2cy86::Instruction& ins,
    const std::set<std::string>& omitted_slots,
    const std::map<std::string, std::string>& promoted_slot_params);
lowir2cy86::Type mir_lookup_type(const lowir2cy86::Function& fn,
                                 const lowir2cy86::Value& value);
std::string reg_for_index(std::size_t index);
std::string abi_gpr(std::size_t index);
std::string value_text(const lowir2cy86::Value& value);
std::string mem_for_offset(std::size_t offset);
std::size_t mir_slot_offset(const lowir2cy86::Function& fn,
                            const std::string& name,
                            const std::set<std::string>& omitted_slots);
std::size_t mir_param_slot_offset(const lowir2cy86::Function& fn,
                                  std::size_t index);
std::string mir_f80_value(const lowir2cy86::Function& fn,
                          const lowir2cy86::Value& value,
                          const std::set<std::string>& omitted_slots);
std::string binary_opcode(const std::string& op);
std::string float_binary_opcode(const std::string& op);
std::string condition_word(const std::string& op);
std::string condition_suffix(const std::string& op);
std::string branch_suffix(const std::string& op);
std::string float_branch_suffix(const std::string& op);

}  // namespace lowir2native
