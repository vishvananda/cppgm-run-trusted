# PA15 Implementation Plan

## Scope

PA15 extends the existing PA12 semantic tree and PA14 LowIR lowerer. The
implementation should keep class/object facts in typed compiler state and add
only the object-model behavior needed by the PA15 contract, leaving copy/value
semantics and polymorphism to later stages.

## Design

- Extend the PA11/PA12 type model with class layout metadata owned by the
  record `Type`: non-static field order, offsets, size, alignment, and the
  single direct base at offset 0.
- Preserve declarations in class scopes as the canonical member table.
  Non-static methods use the existing hidden first `this` parameter shape.
  Static members stay as ordinary class-scope bindings without a hidden
  parameter.
- Resolve `this`, implicit member names inside methods, `.` and `->` through
  typed member bindings. Resolved member nodes carry the selected binding and
  field offset so LowIR lowering does not recover semantics from display text.
- Lower class objects as concrete LowIR storage `obj<bytesxalign>`. Field
  access lowers through `index i8 [projection=field]` using layout offsets,
  then scalar load/store for supported scalar/reference/pointer fields.
- Emit namespace-scope class objects as structured zero data for trivial
  storage, and add `@__cppgm_init` / `@__cppgm_fini` only when object lifetime
  requires helper bodies.
- Emit in-class member definitions as weak LowIR functions, out-of-class member
  definitions as strong functions, and keep deterministic source-level LowIR
  names. Add object metadata only from compiler-owned semantic facts.

## Validation

- Iterate with `make test-report ACTIVE_TEST_REPORT_PAS='pa15'` while fixing
  current-stage failures.
- After each semantic/lowering checkpoint, run
  `make test-report-through-pa15`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa15 --paths dev/src` before
  completion.
- Commit cohesive passing checkpoints and leave the worktree clean.
