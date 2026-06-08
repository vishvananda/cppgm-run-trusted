# PA26 Audit

## Audit Plan

Review the PA26 implementation against `pa26/README.md`,
`TESTING_AND_REFERENCES.md`, `pa26/plan.md`, the PA26 tests, and the
implementation commit `a7ece2f`.

Files and ownership boundaries to inspect:

- `dev/src/pa11_internal.h` and `dev/src/pa11_model.cpp` for durable semantic
  storage of base-subobject paths, member-pointer facts, and ADL owner scopes.
- `dev/src/pa12_internal.h`, `dev/src/pa12_model.cpp`,
  `dev/src/pa12_records.cpp`, `dev/src/pa12_decls*.cpp`,
  `dev/src/pa12_names.cpp`, and `dev/src/pa12_types*.cpp` for record layout,
  base declaration ownership, constructor/member generation, declarator
  parsing, and ambiguity handling.
- `dev/src/pa12_expr*.cpp` for expression ownership of member access,
  member-pointer values, base conversions, overload selection, and reference
  preservation.
- `dev/src/pa12_templates*.cpp` for template argument/value facts,
  pointer-to-member substitution/deduction, specialization identity, ADL, and
  instantiated member ownership.
- `dev/src/pa14_lowir*.cpp` for base-offset lowering, `this` adjustment,
  generated special-member sequencing, pointer-to-member representation,
  `dynamic_cast<void*>`, RTTI facts, and LowIR declaration/function ordering.
- `dev/frontend_source_sets.mk` for source-list coverage of new `.cpp` files.

Risks to audit:

- regressions against PA1-PA25 behavior and unnecessary output perturbation for
  single-base programs;
- skipped compiler phases, fallback success paths, dummy output, embedded
  payloads, host/reference-tool delegation, or test-specific/source-shape gates;
- interpreter/VM/trampoline/template-binary substitutes for required LowIR;
- timeout workarounds, avoidable quadratic lookup/layout scans, repeated
  full-suite walks, excessive copying, and hot-path recomputation;
- stringly semantic facts, duplicated ownership of base/member-pointer facts, or
  downstream recovery of information that should be represented in semantic
  state;
- file-audit warnings in touched PA26 paths, especially large string literals,
  header-body ownership, duplicated implementation blocks, and new source files
  missing from `dev/frontend_source_sets.mk`.

## Findings

- Blocker: `dynamic_cast<void*>` lowered the required vptr offset-to-top path
  but also emitted an unreachable block that called `__dynamic_cast` with
  `void` RTTI. That made the checked-in oracle bless a fallback success path
  and unnecessary runtime/RTTI declarations.
- Blocker: several PA12/PA14 helper paths still inspected only `bare->base`,
  so multi-base records could lose reference-subobject, ABI, storage-copy,
  default-init, zero-init, destructor, global-init, and aggregate child facts
  from later direct bases.
- Reviewed boundary: PA26's non-virtual multi-base helpers use the direct-base
  vector and typed offsets. The older vtable/RTTI routines that still follow a
  primary-base chain are inside the README's single-vptr polymorphic boundary.
- Reviewed cheating/fallback risks: no reference-binary delegation, host
  compiler output generation, interpreter/VM/trampoline substitute, embedded
  earlier-IR payload, test-name gate, timeout workaround, hidden source move, or
  file-audit bypass was found in the audited source paths.

## Changes Made

- Removed the dead `dynamic_cast<void*>` runtime fallback block and the
  `void` RTTI / `__dynamic_cast` declarations from that lowering path, while
  keeping the runtime path for non-void dynamic casts.
- Added an explicit polymorphic-source guard before using the vptr
  offset-to-top slot for `dynamic_cast<void*>`.
- Replaced first-base-only walks with direct-base-vector traversal in reference
  subobject detection, ABI/storage-copy classification, default/copy/move and
  destructor need checks, zero initialization, aggregate child discovery,
  runtime global initialization, and destructor lowering.
- Updated `pa26/tests/general/100-dynamic-cast-void.ref` so the PA26 oracle
  matches the corrected direct object-top lowering instead of the removed dead
  fallback.

## Validation

- `make -C pa26 check TEST=tests/general/100-dynamic-cast-void.t` passed.
- `make test-pa26` passed, 50/50 PA26 local tests.
- `make test-report-through-pa26` passed, 2395/2395 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa26 --paths dev/src` passed with
  22 warnings and no file-audit blocker.
