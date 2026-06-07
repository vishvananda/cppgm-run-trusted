# PA24 Implementation Plan

## Scope

PA24 is an incremental extension of the existing PA12 semantic analyzer and
PA14-PA23 LowIR lowering path. Implementation belongs in `dev/` and
`dev/src/`; PA24 handout, harness, and reference files remain read-only
fixtures.

The target behavior is the PA24 first-tier language closure:

- `auto` variable deduction, including cv-qualified `auto`, pointer and
  reference declarators, and ordinary non-template function/member return
  deduction when the definition body is visible.
- Direct braced initialization for supported scalars, bounded arrays, and
  existing aggregate/object-model cases, including direct braced-init
  expressions and aggregate return/parameter paths.
- Supported conversion closure: non-explicit converting constructors and
  conversion operators in ordinary call/condition contexts, non-class
  functional casts, and pointer/integer `reinterpret_cast`.
- Lambda lowering for captureless lambdas plus the PA24 supported by-reference
  local and `this` capture subset.
- Range-for lowering over bounded arrays, materialized braced lists, and
  supported member/ADL begin/end ranges.

## Ownership Boundaries

- Parser work should only expose already-accepted grammar nodes to the semantic
  layer; it should not create a parallel PA24 parser path.
- Semantic facts must live on typed bindings, types, `Expr`, and `Node`
  metadata already used by PA12/PA14. Lowering should not recover semantics
  from formatted names or source snippets.
- Aggregate constructor synthesis and default member initializer behavior stay
  in the existing declaration/initializer code, with LowIR storage lowering
  reusing `lower_object_init`, `lower_aggregate_init`, and constructor-call
  paths.
- Lambda and range-for support should synthesize ordinary semantic bindings and
  lowered functions/loops on demand, without perturbing PA23 programs that do
  not use those features.

## Work Plan

1. Establish the current PA24 failure surface with the scoped report and inspect
   the first failing clusters against `.ref`/`.ref.exit_status`.
2. Fix the braced initialization and aggregate semantic gaps first, because
   they are shared by auto return, parameter passing, and range/lambda tests.
3. Add `auto` deduction in declarations and visible function definitions,
   preserving declarator spelling semantics for pointer/reference/cv forms.
4. Extend expression conversion/cast handling where PA24 requires ordinary
   class and scalar conversions to participate in calls and conditions.
5. Implement lambda synthesis and range-for lowering on top of the repaired
   initialization and call machinery.
6. Validate after each meaningful shared change with
   `make test-report ACTIVE_TEST_REPORT_PAS='pa24'`, then run
   `make test-report-through-pa24` before completion.
7. Run `perl scripts/cppgm_file_audit.pl --stage pa24 --paths dev/src`, commit
   cohesive progress, and return only with a clean `git status --short`.

## Validation

- `make test-report ACTIVE_TEST_REPORT_PAS='pa24'`: passed, 100/100.
- `make test-report-through-pa24`: passed, 2301/2301.
- `perl scripts/cppgm_file_audit.pl --stage pa24 --paths dev/src`: passed
  with warnings only.
