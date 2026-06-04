# PA19 Implementation Plan

## Scope

PA19 extends the existing PA18 `cppgm++ --emit-lowir` pipeline.  The implementation
must keep parsing, semantic analysis, template instantiation, and LowIR lowering in
`dev/`/`dev/src/`; PA19 tests and references remain harness/oracle material only.

## Design

- Extend the PA12 template model from type-only template arguments to typed
  template arguments that can hold either a type or an integral constant value.
- Parse template parameters with their kind, declared type, pack marker, name,
  and default-token range.  Non-type parameters create value substitutions during
  validation and instantiation, while type parameters keep the existing type
  substitution path.
- Parse template argument lists as type-or-expression arguments.  Reuse the
  existing expression constant folding for literals, enum/static constants,
  casts, `sizeof`, `alignof`, unary/binary/conditional operators, and dependent
  values instead of deriving semantics from formatted names.
- Instantiate class and function templates through the existing PA18 entry
  points, but key/mangle/spell specializations with typed arguments so integral
  values produce distinct declarations and bindings.
- Add semantic handling for `static_assert` declarations and delay evaluation
  when the condition is template-dependent but verify it during concrete
  instantiation.
- Support the PA19 practical pack slice by representing type/value packs in the
  template substitution state and expanding them in supported parameter and call
  forms without changing the LowIR format.
- Preserve PA14 LowIR lowering ownership.  Once templates instantiate to ordinary
  declarations, lowering should consume the existing nodes and binding metadata.
- Keep large PA12 and PA14 mechanics split by ownership: initializer handling,
  id-expression resolution, template instantiation, object initialization, and
  RTTI/vtable emission live in focused source files instead of expanding shared
  parser or program-lowering files.
- Keep function-parameter display names as semantic metadata on function nodes,
  while preserving the source-name bindings used by function bodies.  Explicit
  function specializations can therefore inherit primary-template parameter
  presentation without breaking body lookup.
- Treat instantiated class-template records as ordinary record types with stable
  specialization display names, and let LowIR symbol/RTTI naming derive from that
  typed specialization state.
- Instantiate static member definitions for completed class-template
  specializations, but only emit the constant-member definition forms that become
  concrete global LowIR declarations in this PA19 slice.
- Lower value-initialized generated/defaulted constructors through the existing
  object-init path, zeroing only object graphs that have actual zeroable storage.

## Validation

- Use focused PA19 report runs while diagnosing feature clusters:
  `make test-report ACTIVE_TEST_REPORT_PAS='pa19'`.
- After semantic/lowering checkpoints, run the required through gate:
  `make test-report-through-pa19`.
- Run the file audit after implementation changes:
  `perl scripts/cppgm_file_audit.pl --stage pa19 --paths dev/src`.
- Commit cohesive progress once a stable checkpoint builds and preserves earlier
  assignment behavior.
