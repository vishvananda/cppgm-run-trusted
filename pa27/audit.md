# PA27 Audit

## Audit Plan

- Contract and regression surface:
  - Re-read `pa27/README.md`, `pa27/plan.md`, `TESTING_AND_REFERENCES.md`,
    PA27 local tests, and the recent PA27 implementation commit.
  - Check that PA27 remains a LowIR lowering extension over PA26 rather than a
    new output path, host-toolchain shortcut, interpreter, VM, trampoline,
    embedded-payload, or reference-binary substitute.
  - Spot-check PA26-and-earlier behavior through the required through-stage
    report after any cleanup.
- Source files under audit:
  - Typed object model and layout: `dev/src/pa11_internal.h`,
    `dev/src/pa11_model.cpp`.
  - Semantic base and member ownership: `dev/src/pa12_decls.cpp`,
    `dev/src/pa12_decls_constructor_members.cpp`,
    `dev/src/pa12_decls_members.cpp`, `dev/src/pa12_internal.h`,
    `dev/src/pa12_model.cpp`, `dev/src/pa12_records.cpp`,
    `dev/src/pa12_types_classes.cpp`.
  - LowIR lowering, vtables, RTTI, casts, calls, constructors, initialization,
    and helper splits: `dev/src/pa14_lowir.cpp`,
    `dev/src/pa14_lowir_call.cpp`, `dev/src/pa14_lowir_call_args.cpp`,
    `dev/src/pa14_lowir_conditional.cpp`,
    `dev/src/pa14_lowir_constructor_base_entry.cpp`,
    `dev/src/pa14_lowir_ctor_init.cpp`,
    `dev/src/pa14_lowir_dynamic_cast.cpp`,
    `dev/src/pa14_lowir_init.cpp`,
    `dev/src/pa14_lowir_inline_order.cpp`,
    `dev/src/pa14_lowir_internal.h`,
    `dev/src/pa14_lowir_object_init.cpp`,
    `dev/src/pa14_lowir_program.cpp`,
    `dev/src/pa14_lowir_program_io.cpp`, `dev/src/pa14_lowir_rtti.cpp`,
    `dev/src/pa14_lowir_support.cpp`, `dev/src/pa14_lowir_value_addr.cpp`,
    and `dev/src/pa14_lowir_value_expr.cpp`.
  - Build registration: `dev/frontend_source_sets.mk`.
- Ownership boundaries:
  - Base-specifier facts should be represented in semantic class metadata, not
    recovered from token spelling, AST strings, emitted symbol names, or test
    filenames.
  - Object layout and base-offset queries should remain centralized in PA11 and
    shared PA14 helpers so field access, casts, dispatch, RTTI, and
    constructor/destructor lowering use one model.
  - LowIR-specific vtable, RTTI, thunk, hidden-argument, and construction-table
    logic should stay in PA14 lowering files without mutating PA27 handouts,
    harnesses, references, or checked-output comparators.
- Performance risks to inspect:
  - Recursive base-graph traversals in layout, RTTI, casts, and constructor
    forwarding for avoidable repeated full-graph walks or accidental quadratic
    behavior.
  - Repeated full-program scans while emitting vtables, thunks, VTTs, RTTI, or
    global initialization order.
  - Hot-path string parsing, emitted-symbol decoding, excessive vector copying,
    or recomputation of class layout facts that should already be cached on the
    semantic model.
- File-audit risks to inspect:
  - New or enlarged `dev/src` files against the repository file-audit policy.
  - Hidden implementation fragments outside `dev/src`, source-set omissions for
    newly added `.cpp` files, or weakened audit/test scripts.
  - Any large generated payload, fixture-specific table, copied runtime, or
    implementation moved to unchecked paths.

## Findings

- No skipped compiler phase, reference-binary call, host compiler output path,
  interpreter/VM/trampoline, embedded LowIR payload, fixture-name gate, timeout
  workaround, or PA27 harness/reference edit was found in the PA27-touched
  implementation files.
- Base inheritance facts are represented in typed records: `direct_bases`,
  `direct_base_virtuals`, direct-base offsets, collected virtual bases, and
  virtual-base offsets are owned by PA11 layout and populated by PA12
  base-specifier parsing.
- LowIR vtables, VTTs, RTTI, `dynamic_cast`, `typeid`, virtual dispatch,
  constructor/destructor vptr stores, and field/member access use typed record
  and binding facts rather than test names or emitted-symbol decoding.
- Found duplicated hidden virtual-base lookup logic in
  `dev/src/pa14_lowir_value_addr.cpp`. One copy manually walked function
  parameters and hidden virtual-base slots instead of using the shared helper
  already used by casts and member-call argument lowering.
- Found one avoidable stringly recovery in
  `dev/src/pa14_lowir_constructor_base_entry.cpp`: constructor base-entry
  generation reparsed source parameter names from the LowIR function header.
- File audit passed. The PA27-specific duplicate warning in
  `pa14_lowir_value_addr.cpp` was removed. Remaining warnings are pass-level
  warnings already outside this PA27 cleanup: broad header/body ownership,
  dense older PA14 files, general duplicate blocks outside the audited PA27
  fix, and long LowIR-construction lines that are emitted-instruction text, not
  fixture payloads or executable substitutes.

## Changes Made

- Added this audit file with an explicit Audit Plan before implementation
  edits.
- Centralized hidden virtual-base member-address lowering in
  `dev/src/pa14_lowir_value_addr.cpp` through
  `emit_hidden_virtual_base_addr_for_lvalue`, preserving the canonical
  zero-offset LowIR projection shape expected by PA27 refs.
- Added `FunctionOut::parameter_names` in `dev/src/pa14_lowir_internal.h` and
  populated it in `FunctionLowerer::lower`.
- Replaced LowIR-header parameter-name parsing in
  `dev/src/pa14_lowir_constructor_base_entry.cpp` with the structured
  `FunctionOut::parameter_names` field.
- Updated `pa27/plan.md` with Architecture Review and Final Architecture
  Review sections grounded in the current implementation.

## Validation

- `make build`: pass.
- `make test-pa27`: pass, 26 / 26.
- `make test-report-through-pa27`: pass, 2421 / 2421.
- `perl scripts/cppgm_file_audit.pl --stage pa27 --paths dev/src`: pass with
  24 warnings.
- `git diff --check`: pass.
