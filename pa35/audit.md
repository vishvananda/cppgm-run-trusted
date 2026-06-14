# PA35 Audit

## Audit Plan

- Contract and regression scope: compare the implementation against
  `pa35/README.md`, `TESTING_AND_REFERENCES.md`, the existing `pa35/plan.md`,
  and the PA35 commit history. Treat the required root
  `make test-report-through-pa35` result as the regression gate for PA1 through
  PA35.
- Source files to inspect: the PA35 implementation and audit-refactor changes in
  `dev/include/stdexcept`, `dev/include/typeinfo`, `dev/src/preproc_support.cpp`,
  `dev/src/lowir2cy86_*`, `dev/src/pa11_*`, the parser/semantic/template files
  under `dev/src/pa12_*`, and the hosted object/LowIR path under
  `dev/src/pa14_*`, including new split modules listed in
  `dev/frontend_source_sets.mk`.
- Performance risks to inspect: repeated hosted-header validation, template
  argument substitution and completion loops, function-template instantiation
  replay, overload candidate caching, recursive class-template/type traversal,
  LowIR body-demand closure construction, and any timeout-oriented guard that
  could skip real compiler work instead of reducing redundant work.
- Ownership boundaries to inspect: PA35 must keep implementation in `dev/` and
  `dev/src/`, preserve PA34 hosted preprocessing and PA31-PA34 object emission
  ownership, and keep PA35 heavy-header concessions in typed parser/semantic
  paths rather than in test harnesses, handout files, or copied runtime payloads.
- File-audit issues to inspect: confirm the PA35 file audit is a pass, then
  review its warnings for new oversized or duplicated implementation fragments,
  compressed lines, unchecked source-set additions, large string literals, and
  any apparent movement of implementation into unchecked paths.

## Findings

- No PA35 implementation blocker was found. The stage remains implemented on the
  real `cppgm++ -c` pipeline: hosted preprocessing, PA12 parsing/semantic
  analysis, PA14 LowIR lowering, and the PA31+ host-object emitter.
- Searches of `dev/` and `dev/src` found no PA35 fixture-name gates, reference
  binary invocations, host compiler shell-outs, embedded object payloads,
  interpreter/VM/trampoline substitutes, or dummy object success path. Shelling
  out is confined to test harness/tooling paths, not compiler implementation.
- The hosted compatibility shortcuts inspected are typed and ownership-bounded:
  standard-library template-body validation is deferred after declarations are
  recorded, function-template specializations keep `TemplateArgument` and
  `TypePtr` state, and LowIR body demand preserves object roots/address-taken
  functions instead of bulk-emitting every hosted inline body.
- STL-specific modeling is narrow and semantic: `std::function::operator=`,
  `std::vector::insert`, `std::__write`, `std::basic_string` operators,
  `__gnu_cxx::__normal_iterator`, and `std::shared_ptr` handling are guarded by
  typed namespace/record/template checks rather than source file or test name
  checks.
- The new PA35 refactor modules are listed in `dev/frontend_source_sets.mk`.
  No implementation was moved into `pa35/`, generated outputs, hidden unchecked
  paths, or handout files.
- File audit passes with warnings. The warnings cover known bad-division,
  complexity, duplication, and a compressed `pa14_lowir_init.cpp` line reported
  as a large-literal risk; the inspected warning sites are visible to the audit
  tool and are not bypasses or substitutes for compiler behavior.

## Changes Made

- Added this audit record with the required plan, findings, changes, and
  validation notes.
- Updated `pa35/plan.md` to reflect the current file-audit pass state and added
  `Architecture Review` and `Final Architecture Review` sections grounded in
  the inspected PA35 implementation.
- No compiler source change was needed because the audit found no blocker to
  fix.

## Validation

- `make test-report-through-pa35` passed: `3175 / 3175` tests and all PA1
  through PA35 stages passed.
- `perl scripts/cppgm_file_audit.pl --stage pa35 --paths dev/src` passed with
  24 warnings.
