# PA22 Audit

## Audit Plan

Review the PA22 implementation against the assignment contract, the existing
plan, the PA22 tests, and the `Implement pa22` source footprint. Focus on
whether the compiler still lowers ordinary PA22 template programs through the
semantic and LowIR pipeline rather than by shortcut, fixture-specific behavior,
or hidden payloads.

Files to inspect:

- `dev/src/pa12_decls.cpp`, `dev/src/pa12_decls_declare_one.cpp`,
  `dev/src/pa12_decls_members.cpp`, `dev/src/pa12_records.cpp`, and
  `dev/src/pa12_statements.cpp` for declaration ownership, delayed body/member
  parsing, class completion timing, and regressions in earlier semantic stages.
- `dev/src/pa12_expr*.cpp` for call candidate construction, template-id
  handling, value-category facts, SFINAE expression probes, and hidden fallback
  success paths.
- `dev/src/pa12_templates*.cpp` and `dev/src/pa12_internal.h` for typed
  template argument ownership, deduction, substitution, partial ordering,
  non-type argument representation, and no-eager-instantiation behavior.
- `dev/src/pa12_types.cpp` for type identity/dependency changes that could
  duplicate facts or require downstream string recovery.
- `dev/src/pa14_lowir*.cpp` and `dev/src/pa14_lowir_internal.h` for ordinary
  LowIR lowering of instantiated declarations, constructor entry ownership,
  deterministic emission, and avoidance of dummy/runtime/payload substitutes.
- `dev/frontend_source_sets.mk` for file-list correctness after the new
  `pa12_decls_declare_one.cpp` split.

Performance risks to inspect:

- Repeated full declaration, specialization, overload, or LowIR program scans in
  hot paths introduced for template lookup, instantiation, and emission.
- Quadratic candidate filtering or repeated specialization construction in
  overload resolution and partial ordering.
- Excessive copying of template arguments, parameter bindings, or LowIR text
  when references or cached semantic facts already exist.

Ownership and representation boundaries to inspect:

- Semantic facts should remain in typed declarations, bindings, template
  arguments, expressions, and `TypePtr` values.
- SFINAE/substitution failure should be candidate state until the selected
  context requires a hard diagnostic.
- LowIR should consume semantic declarations and constructor/function entry
  facts; it should not recover template or object-model decisions from emitted
  names.
- Parser/declaration splitting should not create duplicate ownership of pending
  bodies, member declarations, or template parameter scopes.

File-audit issues to inspect:

- New or moved implementation must stay under checked `dev/src` files and be
  listed in `dev/frontend_source_sets.mk` when compiled.
- No implementation fragments should be hidden in `pa22/`, generated fixtures,
  unchecked scripts, binary blobs, or oversized source files that bypass
  `scripts/cppgm_file_audit.pl --stage pa22 --paths dev/src`.

## Findings

- `dev/src/pa14_lowir_program_io.cpp` had a broad
  `demand_synthetic_void_pointer_function()` path that emitted an empty body for
  any demanded non-constructor function with one pointer parameter and `void`
  return. That was a dummy output fallback broader than the typed generated
  constructor case and could hide missing function-body ownership.
- Function-pointer non-type template arguments used `value_binding` for semantic
  matching but converted to PA11 record template arguments with only the
  binding pointer cast to an integer. That raw address leaked into LowIR record,
  RTTI, vtable, and function-specialization metadata names for record template
  cases, making output process-dependent and preserving a stringly/numeric fact
  where a stable binding identity was required.
- The new `dev/src/pa12_templates_instances.cpp` edits initially pushed the file
  over the PA22 file-audit size limit. The helper was tightened in place while
  preserving qualified stable names for non-type binding arguments.
- The remaining inspected fallback/state-restore paths are scoped semantic
  probes: template validation snapshots parser state and restores pending
  bodies, substitutions, and generated tables; SFINAE-style runtime errors are
  candidate drops in overload/conversion selection rather than success outputs.
- No host compiler/reference binary shell-out, embedded payload, unchecked-path
  implementation fragment, fixture-specific source gate, timeout workaround, or
  hidden PA22 implementation under `pa22/` was found.

## Changes Made

- Removed the broad one-pointer `void` synthetic function-definition fallback
  from `ProgramLowerer::demand_function_declaration()`. The remaining empty-body
  synthesis is limited to typed generated default/aggregate constructors.
- Added stable `value_name` ownership to `pa11::TemplateInstanceArgument` and
  populated it from PA12 non-type template arguments that carry a
  `value_binding`.
- Updated PA14 LowIR symbol and RTTI construction to prefer the stable
  non-type binding name instead of the raw integer value when naming record
  specializations, RTTI globals, vtables, and typeinfo strings.
- Updated PA12 function-template ABI argument construction so object metadata for
  function-pointer non-type arguments uses a stable address-of-binding encoding
  instead of a process pointer value.
- Added `cppgm.tests/course/pa22/400-nontype-function-pointer-record-symbol.t`
  with LowIR reference output to cover record, RTTI, and vtable symbol stability
  for function-pointer non-type template arguments.
- Updated `pa22/plan.md` with the required Architecture Review and Final
  Architecture Review sections.

## Validation

- `make test-pa22` passes, including the new course PA22 regression.
- `make test-report-through-pa22` passes: 1682 / 1682 tests, PA1 through PA22.
- `perl scripts/cppgm_file_audit.pl --stage pa22 --paths dev/src` passes with
  10 pre-existing structural warnings and no fatal issues.
- Direct probes for function-pointer non-type template arguments no longer show
  long raw numeric pointer values in record/vtable/RTTI symbols or function
  specialization object metadata.
