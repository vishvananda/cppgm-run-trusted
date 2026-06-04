# PA17 Implementation Plan

## Compiler Design

PA17 extends the PA15/PA16 object model in place. Virtual behavior is owned by
semantic class metadata on `pa11::Type` and `pa11::Binding`, not by LowIR text
inspection or source-shape probes.

- Add typed virtual flags to function bindings: declared virtual, override,
  final, pure virtual, inherited/overriding slot, and deterministic slot index.
- Add record-level polymorphic metadata: whether the class has a primary vptr
  at offset 0, whether the vptr was introduced by this class or inherited from a
  direct base, and the ordered virtual slot list.
- Build vtable layout during class semantic completion from declaration order
  and direct-base metadata. Overrides keep the inherited slot; new virtuals
  append in declaration order; virtual destructors reserve complete and deleting
  slots.
- Keep constructor/destructor lowering in the existing generated/parsed function
  bodies. Constructors write the most-derived vtable address after base
  construction and before member/body work. Destructors write the current class
  vtable address before member/base finalization.
- Emit LowIR vtable and RTTI globals from `ProgramLowerer` based on semantic
  metadata, using deterministic source order and weak/strong binding rules from
  existing function-definition ownership.
- Lower supported virtual member calls by loading the vptr, loading the slot,
  and emitting the existing LowIR indirect call syntax. Explicit qualified calls
  remain direct calls.

## Ownership Boundaries

- `pa11_internal.h` / `pa11_model.cpp`: storage layout and record/function
  metadata fields.
- `pa12_*`: parse and validate `virtual`, `override`, `final`, pure specifiers,
  covariant single-inheritance overrides, and explicit qualification facts on
  call nodes.
- `pa14_lowir_*`: vtable/RTTI emission, vptr stores, and virtual call lowering.
- No PA17 behavior is implemented in test harnesses, refs, wrappers, or by
  calling reference binaries or host compilers.

## Validation Plan

1. Use scoped PA17 report for diagnosis:
   `make test-report ACTIVE_TEST_REPORT_PAS='pa17'`.
2. After semantic/lowering changes, run the required through gate:
   `make test-report-through-pa17`.
3. Run the file audit:
   `perl scripts/cppgm_file_audit.pl --stage pa17 --paths dev/src`.
4. Commit cohesive progress only after the relevant checks are green, and leave
   `git status --short` empty.
