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

## Architecture Review

PA24 is implemented as an extension of the existing PA12 semantic pipeline and
the PA14 LowIR lowering path. `auto` variable and visible-body return deduction
update ordinary `Binding` and `Type` objects before lowering. Braced
initialization and aggregate constructor synthesis reuse the existing record,
initializer, and constructor-action nodes. Lambdas synthesize closure records,
call operators, and helper functions as ordinary semantic artifacts, and
range-for parsing builds typed hidden range/begin/end/index variables plus
`range-for-statement` nodes. PA14 lowers those typed nodes into normal LowIR
storage, calls, and loops.

The audit found one ownership leak in the output-order layer: LowIR function
ordering recovered facts from formatted function headers and slot text. Function
names, strong binding, pointer-result status, and range-for state belong to the
lowered function model, not to downstream parsing of already-emitted text. The
cleanup plan is to carry those facts on `FunctionOut` and have
`pa14_lowir_function_order.cpp` consume typed metadata instead of formatted
strings.

The remaining PA24-specific ordering work is a one-time deterministic output
pass over the lowered functions. It is guarded by function count and does not
run in expression, declaration, overload, or initializer hot paths. No
interpreter, VM, trampoline, copied runtime, embedded earlier-IR payload, test
fixture path, reference-binary shellout, or timeout fallback is part of the PA24
compiler path.

## Final Architecture Review

`FunctionOut` now owns the output facts that were previously recovered from
emitted text: the symbol name, whether a lowered function has range-for
begin/end state, whether it is a strong binding, and whether its LowIR result is
a pointer. The normal `FunctionLowerer` populates those fields while building
the header and slots, and synthetic functions created by the program/RTTI
lowering code set the same fields when they create their `FunctionOut` records.
`pa14_lowir_function_order.cpp` now reads this metadata directly.

The final source review did not find unresolved architecture, performance,
cheating, or regression blockers. PA24 semantic facts are represented before
LowIR lowering, generated lambdas/ranges/aggregate constructors are ordinary
compiler artifacts, and file-audit warnings are dense existing implementation
lines or historical division/duplication warnings rather than hidden payloads or
unchecked implementation fragments.

## Validation

- `make test-report ACTIVE_TEST_REPORT_PAS='pa24'`: passed, 100/100.
- `make test-report-through-pa24`: passed, 2301/2301.
- `perl scripts/cppgm_file_audit.pl --stage pa24 --paths dev/src`: passed
  with warnings only.
