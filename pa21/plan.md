# PA21 Implementation Plan

## Contract

PA21 extends the existing `cppgm++ --emit-lowir -O0` compiler path. The output
format remains PA13 LowIR; this stage owns the semantic model needed for
template declarations, specializations, member/friend templates, and explicit
instantiation to lower through the existing PA14-PA20 machinery.

Implementation changes belong in `dev/` and `dev/src/`. The `pa21/` tree stays
as handout, harness, refs, and this plan.

## Current Evidence

`make test-report-through-pa21` currently passes pa1-pa20 and fails only pa21.
The first failing cases show class partial specializations not being selected
for nested template-id arguments, qualified template-id arguments, and
cv-qualified pointee patterns. Later failures cover template-template
parameters, alias/variable template specialization selection, member templates,
friend templates, and explicit instantiation ownership.

## Design Direction

- Keep template facts in typed semantic structures. Template arguments should
  compare and match by `TypePtr`, constant value, pack contents, and template
  entity identity, not by formatted source text.
- Model class and variable partial specializations as declarations linked to
  the primary template. Instantiate by building a canonical full argument key,
  matching all registered partial candidates, selecting deterministically, and
  using the selected declaration body while caching under the primary key.
- Extend pattern matching recursively over the implemented type surface:
  template parameters, template-template parameters, instantiated class
  template arguments, pointers/references, arrays, function types, and cv
  wrappers. Preserve top-level reference/cv behavior where C++ type identity
  requires it.
- Register member class/function/variable templates and namespace-scope friend
  templates against their owning template declaration/scope. Instantiation
  should preserve the owner links used by normal lookup, access checks, and
  LowIR emission.
- Treat explicit instantiation declarations as suppression of implicit
  materialization and explicit instantiation definitions as requests to emit the
  selected ordinary specialization, reusing the same specialization graph.

## Ownership Boundaries

- Parser and semantic changes: `dev/src/pa12_*.cpp`, `dev/src/pa12_internal.h`,
  and existing PA11 type helpers if type identity/matching needs support.
- LowIR changes should be limited to cases where the semantic model already
  produces the correct ordinary binding/type but emission lacks a generic
  path. Do not add fixture-specific emission.
- If a new source file becomes necessary, add it to `dev/frontend_source_sets.mk`
  with the appropriate frontend source set.

## Validation Plan

1. Use focused `make -C pa21 check TEST=...` and
   `make test-report ACTIVE_TEST_REPORT_PAS='pa21'` while diagnosing pa21-only
   failures.
2. After each semantic/lowering checkpoint, run root
   `make test-report-through-pa21` to catch older-stage regressions.
3. Run `perl scripts/cppgm_file_audit.pl --stage pa21 --paths dev/src`.
4. Commit cohesive progress once the through check and file audit pass, then
   verify `git status --short` is empty.
