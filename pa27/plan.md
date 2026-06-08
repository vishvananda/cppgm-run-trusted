# PA27 Implementation Plan

## Scope

PA27 extends the existing PA26 source-to-LowIR compiler path in `dev/src`.
The implementation stays in the shared parser, semantic model, layout, and
LowIR lowering code so later assignments inherit the same object model.

## Design

- Extend typed class metadata to retain every direct base and whether that edge
  is virtual. Avoid recovering base facts from AST text or emitted symbol names.
- Layout complete objects with deterministic direct-base offsets, one shared
  subobject for each reachable virtual base, and primary-vptr behavior that
  preserves PA26 single-base cases.
- Build vtable and RTTI data from the typed base graph. Classes with multiple
  relevant bases should emit VMI RTTI and secondary vtable views for
  non-primary polymorphic bases, including this-adjusting thunks where a slot is
  reached through a non-primary view.
- For polymorphic classes with virtual bases, use the Itanium-style address
  point shape required by the course LowIR refs: primary and secondary views
  carry vbase-offset, offset-to-top, and RTTI header entries, and construction
  vtables/VTTs pass subobject-specific address points into base constructors and
  destructors.
- Route base-subobject address calculations, field/member access, constructor
  forwarding, static casts, pointer/reference downcasts, `dynamic_cast<T*>`,
  `typeid(expr)`, and virtual dispatch through the same base-offset helpers.
- Keep constructor/destructor vptr stores attached to real construction and
  destruction lowering, emitting all needed base views without changing
  harnesses or fixture expectations.

## Ownership Boundaries

- Parser/semantic changes live in `pa12_*` only where base-specifier facts,
  generated constructor/destructor actions, or virtual override tables are
  created.
- Layout and base-query helpers live in the PA11 model and PA14 shared support
  helpers.
- LowIR-specific vtable, RTTI, cast, call, and object initialization changes
  live in `pa14_lowir_*`.
- Keep audit-driven source splits mechanical: move self-contained LowIR helper
  groups into new `pa14_lowir_*` files and add them to
  `dev/frontend_source_sets.mk`, without changing generated IR semantics.
- No PA27 test files or reference files are implementation targets.

## Validation

- Use `make test-report ACTIVE_TEST_REPORT_PAS='pa27'` for focused diagnosis.
- After meaningful compiler changes, run `make test-report-through-pa27`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa27 --paths dev/src`.
- Commit only cohesive compiler progress and leave `git status --short` clean.

## Final Results

- `make test-report ACTIVE_TEST_REPORT_PAS='pa27'`: pass, 26 / 26.
- `make test-report-through-pa27`: pass, 2421 / 2421.
- `perl scripts/cppgm_file_audit.pl --stage pa27 --paths dev/src`: pass
  with warnings only.
