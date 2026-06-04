# PA17 Audit

## Audit Plan

Review PA17 against `pa17/README.md`, `pa17/plan.md`, recent commits, the
local PA17 suites under `pa17/tests/general/` and `pa17/tests/spec/`, and the
source files changed by `Implement PA17 virtual dispatch`.

Files and ownership boundaries to inspect:

- Semantic model ownership in `dev/src/pa11_internal.h` and
  `dev/src/pa11_model.cpp`: typed storage for virtual function state, vptr
  ownership, and ordered vtable entries.
- Declaration/type semantic ownership in `dev/src/pa12_decls.cpp`,
  `dev/src/pa12_decls_members.cpp`, `dev/src/pa12_types.cpp`,
  `dev/src/pa12_records.cpp`, `dev/src/pa12_expr_nodes.cpp`,
  `dev/src/pa12_expr_semantics.cpp`, `dev/src/pa12_statements.cpp`,
  `dev/src/pa12_support.cpp`, and `dev/src/pa12_internal.h`: parsing and
  validation of `virtual`, `override`, `final`, pure specifiers, explicit
  qualification, override matching, inherited virtual destructors, and class
  completion.
- LowIR ownership in `dev/src/pa14_lowir.cpp`,
  `dev/src/pa14_lowir_call.cpp`, `dev/src/pa14_lowir_init.cpp`,
  `dev/src/pa14_lowir_program.cpp`, `dev/src/pa14_lowir_support.cpp`,
  `dev/src/pa14_lowir_value_expr.cpp`, and `dev/src/pa14_lowir_internal.h`:
  vtable/RTTI emission, vptr stores, indirect virtual calls, virtual
  destructor calls, and interaction with PA14-PA16 lowering.
- Source-set and file-audit surface: confirm no PA17 code was moved outside
  `dev/src`, no unchecked helper fragments or generated payloads were added,
  no new `dev/src/*.cpp` files are missing from `dev/frontend_source_sets.mk`,
  and `perl scripts/cppgm_file_audit.pl --stage pa17 --paths dev/src` remains
  green.

Performance and architecture risks to inspect:

- Vtable construction and override lookup should be bounded by class/member
  metadata already in memory, not repeated full-program scans or source-text
  rediscovery during lowering.
- LowIR vtable emission should be demand driven and deduplicated without
  repeatedly walking the entire test suite or filesystem.
- Virtual call lowering should use semantic `virtual_dispatch` facts and slot
  indices, not string tests on source names or LowIR text.
- Constructor/destructor vptr stores should remain in the existing object
  lifetime lowering path, without alternate trampoline/interpreter/runtime
  substitutes.
- Earlier PA behavior for non-polymorphic code should remain a monotonic PA16
  path: no eager vtable emission, no fallback success paths, and no test-shape
  acceptance gates.

## Findings

- Found a PA17 layout blocker for polymorphic derived classes with a
  data-bearing non-polymorphic direct base. The class introduced its vptr at
  object offset 0, but all base-subobject projections were still hardcoded to
  offset 0. Base construction could initialize a base field at offset 0, and
  the derived constructor then overwrote the same bytes with the vptr. Base
  member calls, pointer conversions, and reference conversions also reused the
  derived object address instead of the base subobject address.
- No skipped compiler phase, dummy/minimal output generator, interpreter, VM,
  trampoline, template-binary, copied-runtime, embedded-payload substitute,
  reference-binary shellout, host-compiler shellout, timeout workaround,
  fixture-specific gate, or file-audit bypass was found in the PA17
  implementation.
- Vtable construction, override lookup, virtual call lowering, vtable demand
  emission, and vptr stores are owned by semantic class/function metadata and
  demand-emitted record/function sets. The audited paths do not perform
  repeated full-suite walks or filesystem scans.
- The remaining `Node::line` dispatch is the existing PA10/PA14 AST boundary.
  PA17 virtual facts are not recovered from LowIR text; they are carried as
  binding flags, vtable entries, slot indices, and explicit expression flags.

## Changes Made

- Added `pa11::Type::direct_base_offset` and taught record layout to place a
  storage-bearing non-polymorphic base after the newly introduced vptr while
  preserving offset-zero empty-base behavior and inherited-polymorphic-base
  behavior.
- Added a PA14 base-subobject offset helper that walks the supported
  single-inheritance chain and uses layout-owned direct-base offsets.
- Replaced hardcoded offset-zero base projections in constructor base init,
  destructor base finalization, generated deleting destructor entries,
  defaulted assignment lowering, aggregate/object zero initialization,
  base-member address lowering, derived-to-base pointer conversion, and
  derived-to-base reference conversion.
- Added course regression
  `cppgm.tests/course/pa17/general/500-nonpolymorphic-base-data-vptr-offset.t`
  with LowIR refs that assert offset-8 base projections and `obj<16x8>` layout
  for a data-bearing non-polymorphic base under a polymorphic derived class.

## Validation

- `make -C dev cppgm++`: pass.
- Focused manual LowIR checks for data-bearing non-polymorphic base under a
  polymorphic derived class: pass; constructors, virtual member body base
  access, pointer conversion, and reference conversion project the base
  subobject at offset 8.
- `make test-pa17`: pass, including 22 local PA17 tests and 1 PA17 course
  regression test.
- `perl scripts/cppgm_file_audit.pl --stage pa17 --paths dev/src`: pass with
  the repository's existing 6 warnings.
- Required `make test-report-through-pa17`: pass, 1166/1166 tests across PA1
  through PA17.
