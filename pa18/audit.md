# PA18 audit

## Audit Plan

- Re-read the PA18 contract in `pa18/README.md`, the repository testing rules in
  `TESTING_AND_REFERENCES.md`, and the current implementation notes in
  `pa18/plan.md` before touching implementation code.
- Inspect the PA18 implementation commit and changed files:
  `dev/frontend_source_sets.mk`, `dev/src/pa11_internal.h`,
  `dev/src/pa11_model.cpp`, `dev/src/pa12_internal.h`,
  `dev/src/pa12_model.cpp`, `dev/src/pa12_decls.cpp`,
  `dev/src/pa12_decls_members.cpp`, `dev/src/pa12_names.cpp`,
  `dev/src/pa12_records.cpp`, `dev/src/pa12_types.cpp`,
  `dev/src/pa12_expr*.cpp`, `dev/src/pa12_statements.cpp`,
  `dev/src/pa12_support.cpp`, `dev/src/pa12_templates.cpp`,
  `dev/src/pa12_templates_functions.cpp`, and the PA14 LowIR changes in
  `dev/src/pa14_lowir*.cpp` / `dev/src/pa14_lowir_internal.h`.
- Check ownership boundaries: template declarations and instantiations must be
  owned by PA12 semantic state, instantiated class/function entities must lower
  through ordinary PA15-PA17 metadata, temporary template/function scopes must
  not leak names, and PA14 must only demand already-modeled semantic entities.
- Check cheating and skipped-phase risks: no fallback success paths, dummy or
  minimal LowIR, template-binary/runtime payloads, interpreter/VM/trampoline
  substitutes, source-shape test gates, reference-binary shell-outs, or weakened
  error handling.
- Check semantic fact representation: avoid string-only type/template facts,
  duplicated ownership of class/function state, downstream reconstruction of
  facts that PA12 should model, and brittle current-instantiation or dependent
  lookup shortcuts.
- Check performance risks: repeated full-suite/source walks, avoidable quadratic
  overload/template scans, excessive token/type copying, uncached instantiation
  or LowIR closure work, and hot-path recomputation during lookup, deduction,
  class completion, and weak inline function emission.
- Check file-audit risks: new `dev/src/*.cpp` registration, hidden
  implementation fragments outside audited paths, file-size pressure,
  audit-bypass movement, generated payloads, or changes to audit/test harnesses.
- Review relevant PA18 tests and earlier-stage regression coverage, then run the
  required exits: `make test-report-through-pa18` and
  `perl scripts/cppgm_file_audit.pl --stage pa18 --paths dev/src`.

## Findings

- PA14 was treating record-name spelling containing `<` as the semantic marker
  for class-template specialization context. That affected inline emission and
  constructor/destructor ordering decisions, so it was a stringly semantic fact.
- Class-template validation parsed against real PA12 owner scopes and left
  validation-only class scopes, type bindings, generated/default tables, and
  possible dependent specialization shells behind. That was an ownership leak,
  even when it did not emit LowIR.
- Moving validation state into the original `pa12_templates.cpp` exceeded the
  PA18 file-audit size/function-size limits. Keeping that code in the same file
  would have been a file-audit blocker.
- No reference-binary shell-outs, fixture gates, embedded payloads, trampoline or
  interpreter substitutes, dummy LowIR outputs, timeout workarounds, or hidden
  unchecked implementation paths were found.

## Changes Made

- Added `pa11::Type::is_template_specialization` and set it when PA12 creates a
  class-template specialization.
- Replaced PA14 template-specialization name scans with
  `record_is_template_specialization` and
  `binding_has_template_specialization_context`.
- Moved side-effect-contained class-template validation into
  `dev/src/pa12_templates_validation.cpp`, registered it in
  `dev/frontend_source_sets.mk`, and made validation restore PA12 semantic state
  after parsing against a temporary owner scope.
- Removed the validation-only dummy binding path from `pa12_templates.cpp`.

## Validation

- `make test-report ACTIVE_TEST_REPORT_PAS='pa18'`: passed, 194/194.
- `make test-report-through-pa18`: passed, 1360/1360.
- `perl scripts/cppgm_file_audit.pl --stage pa18 --paths dev/src`: passed with
  six pre-existing warnings and no fatal issues.
- `git diff --check`: passed.
