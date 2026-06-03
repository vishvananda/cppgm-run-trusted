#pragma once

// Lightweight PA30-facing ABI fact interface. The PA30 implementation should
// own the concrete fact model and mangling logic in compiled .cpp files rather
// than keeping a large implementation body in this shared header.

#include <string>
#include <vector>

namespace abi_mangle {

enum AbiMangleTargetKind
{
  ABI_MANGLE_NONE,
  ABI_MANGLE_TYPE,
  ABI_MANGLE_FUNCTION,
  ABI_MANGLE_VARIABLE,
  ABI_MANGLE_TYPEINFO,
  ABI_MANGLE_VTABLE,
  ABI_MANGLE_VTT,
  ABI_MANGLE_CONSTRUCTION_VTABLE,
  ABI_MANGLE_THREAD_LOCAL_WRAPPER,
  ABI_MANGLE_THUNK,
  ABI_MANGLE_VIRTUAL_BASE_THUNK
};

struct AbiFact
{
  std::string id;
  std::string kind;
  std::vector<std::string> fields;
};

struct AbiMangleTarget
{
  AbiMangleTargetKind kind;
  std::string symbol;

  AbiMangleTarget()
      : kind(ABI_MANGLE_NONE)
  {
  }
};

struct AbiFactCase
{
  std::string label;
  std::vector<AbiFact> facts;
  AbiMangleTarget target;
};

struct AbiFactFile
{
  std::vector<AbiFactCase> cases;
};

AbiFactFile parse_fact_text(const std::string & text);
std::string serialize_fact_file(const AbiFactFile & file);
std::string mangle_fact_file(const AbiFactFile & file);
std::string mangle_fact_files(const std::vector<std::string> & input_paths);

}  // namespace abi_mangle
