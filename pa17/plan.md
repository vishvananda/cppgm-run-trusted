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

## Architecture Review

The implemented PA17 path matches the planned ownership split. `pa11::Binding`
owns virtual flags, override links, slot indices, and slot widths; `pa11::Type`
owns record polymorphism state, vptr introduction state, ordered vtable
entries, and the direct-base layout offset used when a PA17 vptr is introduced
ahead of a storage-bearing non-polymorphic base. Class completion in
`pa12_decls.cpp` builds vtable entries from direct-base metadata and class
binding order, with overrides replacing inherited entries in place and virtual
destructors occupying complete/deleting slot pairs.

The PA12 layer parses `virtual`, `override`, `final`, and pure specifiers into
semantic binding fields. It records explicit qualification as
`suppress_virtual_dispatch` on expression nodes, then call semantics records the
selected binding and the `virtual_dispatch` decision. LowIR lowering consumes
those semantic facts: direct calls remain direct, while virtual calls load the
object vptr, index the selected slot, load the function pointer, and emit the
existing indirect call form.

The PA14 layer emits vtables and RTTI through `ProgramLowerer::demand_vtable`,
deduplicated by record identity and driven by semantic polymorphism metadata.
Constructors and destructors write vptrs in the existing lifetime-lowering
flow, not through a separate runtime, interpreter, trampoline, or copied
payload. Base-subobject projection is now layout-owned: `pa11::Type` stores the
direct base offset, and `pa14` computes derived-to-base offsets from the
single-inheritance chain instead of hardcoding offset zero in each lowering
site.

## Final Architecture Review

After audit cleanup, PA17 remains a monotonic extension of PA16. Non-polymorphic
classes do not get eager vtables or vptr stores. Polymorphic classes with
polymorphic direct bases keep the inherited vptr at offset zero. Polymorphic
classes that introduce the first vptr while inheriting storage from a
non-polymorphic direct base keep the vptr at offset zero and place the base
subobject after the vptr with alignment padding, so base construction, base
member access, derived-to-base pointer/reference conversion, copy/assignment,
and destruction all agree on one semantic layout fact.

No PA17 behavior is implemented in harnesses, wrappers, unchecked paths, or by
calling reference binaries or host compilers. The remaining string dispatch on
`Node::line` is the established PA10/PA14 AST representation boundary; PA17
virtual semantics themselves are represented by binding fields, vtable slot
metadata, and explicit `virtual_dispatch`/`suppress_virtual_dispatch` flags.
The audited hot paths are bounded by class hierarchy depth, class member count,
or demand-emitted record identity sets; no repeated full-suite walks, timeout
workarounds, fallback success paths, or test-shape acceptance gates were found.
