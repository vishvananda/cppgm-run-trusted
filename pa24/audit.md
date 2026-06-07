# PA24 Audit

## Audit Plan

Audit target: PA24 full-stage `cppgm++ --emit-lowir` implementation in
`dev/` and `dev/src/`, with the PA24 handout, `pa24/plan.md`, recent commits,
and PA24 tests as the contract.

Files to inspect:

- Semantic declaration and initializer ownership:
  `dev/src/pa12_decls.cpp`, `dev/src/pa12_decls_declare_one.cpp`,
  `dev/src/pa12_decls_initializers.cpp`, `dev/src/pa12_records.cpp`,
  `dev/src/pa12_statements.cpp`, and `dev/src/pa12_internal.h`.
- Expression typing, conversions, casts, lambdas, and call helpers:
  `dev/src/pa12_expr.cpp`, `dev/src/pa12_expr_call_helpers.cpp`,
  `dev/src/pa12_expr_ids.cpp`, `dev/src/pa12_expr_nodes.cpp`,
  `dev/src/pa12_expr_primary.cpp`,
  `dev/src/pa12_expr_semantics.cpp`,
  `dev/src/pa12_expr_semantics_constructors.cpp`, and related template
  validation/deduction changes.
- LowIR lowering and output ordering:
  `dev/src/pa14_lowir.cpp`, `dev/src/pa14_lowir_call.cpp`,
  `dev/src/pa14_lowir_ctor_init.cpp`,
  `dev/src/pa14_lowir_function_order.cpp`,
  `dev/src/pa14_lowir_globals.cpp`, `dev/src/pa14_lowir_init.cpp`,
  `dev/src/pa14_lowir_inline_order.cpp`,
  `dev/src/pa14_lowir_internal.h`,
  `dev/src/pa14_lowir_object_init.cpp`,
  `dev/src/pa14_lowir_program.cpp`,
  `dev/src/pa14_lowir_program_io.cpp`,
  `dev/src/pa14_lowir_rtti.cpp`,
  `dev/src/pa14_lowir_support.cpp`,
  `dev/src/pa14_lowir_value_addr.cpp`, and
  `dev/src/pa14_lowir_value_expr.cpp`.
- Build/source-set integration:
  `dev/frontend_source_sets.mk` and `dev/src/posttoken_support.cpp`.

Performance risks to inspect:

- Repeated full-program walks introduced by LowIR function/inline ordering,
  especially recursive dependency collection and queue membership tests.
- Range-for and lambda lowering paths that might rescan all statements,
  functions, captures, or globals per expression instead of carrying typed
  semantic metadata.
- Braced aggregate/array initialization paths that may repeatedly copy
  initializer vectors, members, or type layouts.
- Call conversion and constructor lookup paths that might add avoidable
  quadratic overload scans on ordinary earlier-PA calls.

Ownership and semantic risks to inspect:

- `auto`, braced-init, range-for, lambda, cast, and conversion facts should be
  represented in PA12 semantic objects and expression metadata before LowIR
  lowering; PA14 should not recover semantics from source snippets, formatted
  names, or test-specific symbol text.
- Lambda helpers, range temporaries, aggregate initialization, and synthesized
  constructors/destructors should be ordinary compiler artifacts owned by the
  existing semantic/lowering pipeline, not interpreter, VM, trampoline,
  template-binary, copied-runtime, or embedded-payload substitutes.
- PA24 behavior must be on demand and should not perturb PA23 source programs
  that do not use the new feature slice.
- Output ordering must be deterministic without hiding missing declarations or
  relying on relaxed comparison to mask incomplete LowIR.

File-audit issues to inspect:

- Current `cppgm_file_audit.pl --stage pa24 --paths dev/src` passes but reports
  warnings for large headers/catch-all files, duplicate blocks, and large
  string literals in `pa12_expr_ids.cpp`, `pa12_expr_nodes.cpp`, and
  `pa14_lowir_init.cpp`.
- Confirm the warnings are pre-existing structure or legitimate generated text
  tables, not PA24 hidden implementation fragments, fixture payloads,
  weakened checks, or code moved outside audited paths.

## Findings

- Fixed blocker: `pa14_lowir_function_order.cpp` recovered lowered-function
  facts from formatted output strings. It parsed `FunctionOut.header` for the
  function name and binding/return markers, and scanned formatted slot text for
  range-for `__begin`/`__end` state. That duplicated semantic ownership and made
  deterministic ordering depend on emitted spelling.
- PA12 owns the PA24 semantic facts before lowering. `auto` declarations and
  visible-body return deduction update typed bindings; aggregate and braced
  initialization synthesize constructor/action nodes; lambda parsing builds
  closure records, call operators, helper functions, and capture initializers;
  range-for parsing builds typed hidden variables and `range-for-statement`
  nodes.
- PA14 lowers the typed artifacts into ordinary LowIR. Range-for lowers to
  explicit loops, lambda/aggregate closure initialization uses the existing
  object initialization path, and RTTI handles lambda type names from generated
  semantic symbols.
- No skipped compiler phase, fallback success path, dummy/minimal output,
  interpreter/VM/trampoline substitute, copied runtime, embedded payload,
  reference-binary shellout, test-fixture gate, or timeout workaround was found
  in the PA24 compiler source path.
- Performance review found no PA24 hot-path full-suite walk. The remaining
  function-order passes are one-time deterministic output ordering over lowered
  functions and are guarded by function count; the fixed issue removed
  avoidable repeated header/slot text recovery from those passes.
- File-audit warnings were inspected. The large-string warnings at
  `pa12_expr_ids.cpp`, `pa12_expr_nodes.cpp`, and `pa14_lowir_init.cpp` are
  dense implementation lines that construct semantic/LowIR text, not fixture
  payloads or embedded compiler output. The remaining warnings are existing
  division/duplication/complexity warnings, and fileAudit still passes.

## Changes Made

- Added typed `FunctionOut` metadata for symbol name, range-for state, strong
  binding, and pointer-result status.
- Populated that metadata in normal function lowering and synthetic function
  creation paths, including constructor base/no-op entries, synthetic
  assignment helpers, empty member functions, and deleting destructor entries.
- Updated LowIR function ordering to consume the metadata instead of parsing
  formatted headers or slots.
- Updated `pa24/plan.md` with Architecture Review and Final Architecture
  Review sections.

## Validation

- `make test-pa24`: passed, 100/100 after the metadata cleanup.
- `make test-report-through-pa24`: passed, 2301/2301.
- `perl scripts/cppgm_file_audit.pl --stage pa24 --paths dev/src`: passed
  with 22 warnings inspected above.
