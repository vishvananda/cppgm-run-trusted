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

## Architecture Review

The implemented PA15 stage follows the intended PA14 extension path rather than
adding a separate backend. Class layout lives in the PA11 `Type` record state:
`layout_record_type` computes and caches field order, offsets, bit-field
positions, size, alignment, and the single direct base. PA12 owns name lookup,
access checks, friend/hidden-friend state, `this` binding, member expression
selection, constructor/destructor discovery, and generated lifetime action
nodes. The LowIR lowerer consumes those bindings and type facts; field and base
projections use `Binding::member_offset`, `Binding::bit_offset`, and the direct
base at offset zero instead of recovering offsets from emitted text.

The PA15 helper model is demand-driven. Inline member functions, generated
default constructors, aggregate constructors, destructors, and namespace-scope
init/fini helpers are registered by binding and emitted only when the parsed
program requires them. Local cleanups are represented as scoped cleanup stacks
in `FunctionLowerer`; global lifetime is collected into `@__cppgm_init` and
`@__cppgm_fini` bodies only when runtime initialization or finalization is
needed. New PA14 lowering implementation files are present in
`dev/frontend_source_sets.mk`.

Performance review found no full-suite walks, fixture-name gates, or repeated
whole-translation-unit recomputation in the PA15 paths. The remaining scans are
bounded to current scope/member vectors, direct-base chains, or initializer
clauses. Layout and helper emission use cached `layout_valid` state and
generated-helper sets to avoid repeated layout and duplicate helper bodies.

## Final Architecture Review

The audited implementation keeps the PA15 ownership boundary intact: PA11 owns
type/layout facts, PA12 owns semantic binding and lifetime-action construction,
and PA14 owns LowIR presentation and helper emission. The review did not find
interpreter, VM, trampoline, template-binary, embedded-payload, reference-tool,
timeout, or test-fixture substitutes in the PA15 source surface.

Audit cleanup was limited to misleading indentation in the PA12 declaration,
record-helper, class-body, and PA14 initializer/lifecycle lowering code. The
cleanup did not change the semantic model or output contract, but it makes the
audited constructor/destructor and aggregate-initialization control flow match
the actual block structure for future stages.
