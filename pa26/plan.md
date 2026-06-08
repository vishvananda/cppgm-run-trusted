# PA26 Implementation Plan

## Scope

PA26 extends the existing PA25 compiler path. Implementation stays in `dev/`
and `dev/src/`; the PA26 directory remains tests, scripts, refs, and this plan.

The required feature surface is:

- non-virtual multiple-base class layout with deterministic base offsets
- inherited field and method lookup through multiple base subobjects, including
  ambiguity rejection
- generated constructors, copy/move, assignment, and destruction over all
  supported non-virtual bases
- `dynamic_cast<void*>` for the existing single-vptr polymorphic ABI
- pointer-to-member object/function types, values, conversions, and `.*` /
  `->*` lowering needed by the PA26 tests

## Design

- Keep semantic ownership in PA11/PA12 record, type, binding, and expression
  state. Base-subobject paths, member-owner classes, pointer-to-member classes,
  and member-pointer constants should be represented as typed facts instead of
  inferred back from formatted AST text.
- Extend record layout helpers to iterate all direct non-virtual bases in
  declaration order. Keep the existing single-base fields valid for old code
  while using the base-vector data for PA26 behavior.
- Make member lookup collect candidates by declaration owner and reachable
  subobject path. A name found in more than one incomparable base subobject is
  ambiguous unless a derived declaration hides the inherited set.
- Lower base-derived conversions and member access by applying the recorded
  subobject offset path. Method calls must adjust the implicit object argument
  to the class that owns the selected member function.
- Represent data member pointers as byte offsets with a null sentinel, and
  represent member function pointers as the selected non-virtual function
  symbol plus the required this-adjustment. Base-to-derived member-pointer
  conversions add the derived-to-base offset.
- Generate default/copy/move/assignment/destruction bodies by sequencing all
  direct bases before/after fields in C++ order, preserving earlier PA outputs
  for single-base programs where possible.
- Lower `dynamic_cast<void*>` through the existing vptr/RTTI object-top path for
  the current single-polymorphic-base ABI only; broader multiple-polymorphic
  cases remain PA27 work.
- Preserve ADL ownership for forward-declared record types by tracking each
  record type's declaring scope separately from its definition scope. Associated
  namespace lookup uses this owner map when a record has no class scope yet, so
  template arguments such as `detail::file_tag` still contribute `detail` to
  ADL.
- Keep LowIR function ordering based on typed binding relationships plus actual
  lowered call references. When same-owner local/template helpers are emitted
  out of reference order, reorder constructor and `operator()` definitions to
  match the caller's call order without changing generated code.

## Architecture Review

- The implementation keeps PA26 ownership in the existing semantic pipeline:
  `Type::direct_bases`, base offsets, selected member owners, base conversion
  paths, and member-pointer classes are typed semantic facts rather than LowIR
  text recovered downstream.
- PA26 direct-base layout is centralized in PA11 record layout helpers, with
  `record_direct_bases` preserving compatibility for older single-base code.
  LowIR lowering uses `emit_base_subobject_addr` / direct-base offsets instead
  of ad hoc byte constants at call sites.
- Generated default, copy/move, assignment, destructor, aggregate, zero-init,
  ABI-classification, cleanup, and global-init helpers must walk all direct
  bases in declaration/destruction order. Audit cleanup closed remaining
  first-base-only walks in the shared PA12/PA14 helper paths.
- `dynamic_cast<void*>` is a PA26-only RTTI slice over the existing single-vptr
  ABI. It now lowers directly through the vptr offset-to-top slot for
  polymorphic source records and does not emit an unreachable runtime
  `__dynamic_cast` fallback block for this case.
- The reviewed source paths do not shell out to reference binaries, host
  compilers, interpreters, VMs, trampolines, copied runtime payloads, or
  templated LowIR blobs to satisfy PA26 output.
- Performance-sensitive PA26 operations use stored base vectors, layout caches,
  selected binding facts, and actual call-reference ordering. The audit did not
  find timeout knobs, repeated full-suite walks, or new hot-path quadratic scans
  in the changed implementation.

## Final Architecture Review

- After cleanup, the PA26 architecture matches the README boundary: supported
  non-virtual multiple-base layout, lookup, this adjustment, generated special
  members, pointer-to-member lowering, and `dynamic_cast<void*>` stay inside
  the normal semantic and LowIR generation pipeline.
- The remaining single-vptr polymorphic code is kept behind the assignment
  boundary. PA26 direct-base object-model helpers use all direct bases; older
  single-primary-base RTTI/vtable routines remain scoped to the README's
  existing ABI limit.
- The corrected `dynamic_cast<void*>` reference records the required object-top
  lowering and no longer blesses a dead runtime fallback success path.
- No architecture, performance, regression, cheating, or file-audit blockers
  remain from this audit pass.

## Validation

- Use scoped PA26 report runs during diagnosis:
  `make test-report ACTIVE_TEST_REPORT_PAS='pa26'`.
- After meaningful semantic or lowering edits, run
  `make test-report-through-pa26`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa26 --paths dev/src`.
- Commit cohesive progress only after a stable checkpoint, and leave
  `git status --short` clean when complete.

## Current Audit Cleanup

- Remove the unreachable `dynamic_cast<void*>` runtime fallback so the PA26
  object-top lowering is the only generated path for that assignment feature.
- Finish converting first-base-only generated-member, zero-init, destructor,
  ABI, and aggregate helper walks to direct-base-vector traversal.
- Keep the oracle update limited to the semantic LowIR delta for
  `100-dynamic-cast-void`: no dead fallback block and no unused `void` RTTI /
  `__dynamic_cast` declarations.
