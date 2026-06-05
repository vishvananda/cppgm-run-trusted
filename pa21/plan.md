# PA21 Implementation Plan

## Contract

PA21 extends the existing `cppgm++ --emit-lowir -O0` compiler path. The output
format remains PA13 LowIR; this stage owns the semantic model needed for
template declarations, specializations, member/friend templates, and explicit
instantiation to lower through the existing PA14-PA20 machinery.

Implementation changes belong in `dev/` and `dev/src/`. The `pa21/` tree stays
as handout, harness, refs, and this plan.

## Current Evidence

The semantic and LowIR implementation now passes the PA21 scoped report and the
root `make test-report-through-pa21` gate. The PA21 file audit also passes after
splitting large parser/semantic helper groups into focused `dev/src/*.cpp`
ownership units and tightening a few overlong LowIR lowering functions.

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
- Capture enclosing class-template substitutions on nested template
  declarations. Member function templates should instantiate lazily from that
  captured owner context, while constructor templates remain discoverable through
  constructor overload resolution so earlier constructor behavior is preserved.
- Propagate expression packs as typed expression nodes through functional casts,
  calls, casts, binary expressions, and address-of expansions. Pack expansion
  should be driven by template-argument and expression-pack structure rather
  than source-shape checks.
- Keep dependent `template` disambiguator handling in the parser/name resolver,
  then let ordinary lookup and substitution find the final template entity.
  Do not recover owner or function identity from formatted qualified names.

## Ownership Boundaries

- Parser and semantic changes: `dev/src/pa12_*.cpp`, `dev/src/pa12_internal.h`,
  and existing PA11 type helpers if type identity/matching needs support.
- LowIR changes should be limited to cases where the semantic model already
  produces the correct ordinary binding/type but emission lacks a generic
  path. Do not add fixture-specific emission.
- Local-static and function-specialization LowIR naming fixes should attach the
  owning semantic binding during semantic/lowering setup; LowIR should not infer
  template identity by parsing generated symbol text.
- If a new source file becomes necessary, add it to `dev/frontend_source_sets.mk`
  with the appropriate frontend source set.
- Audit refactors should be behavior-preserving. Prefer moving complete parser
  or semantic method groups into focused `dev/src/*.cpp` files and extracting
  helpers from oversized functions over rewriting logic while tests are green.

## Validation Plan

1. Use focused `make -C pa21 check TEST=...` and
   `make test-report ACTIVE_TEST_REPORT_PAS='pa21'` while diagnosing pa21-only
   failures.
2. After meaningful parser, semantic, or LowIR checkpoints, run root
   `make test-report-through-pa21` to catch older-stage regressions before
   treating PA21 progress as stable.
3. Run `perl scripts/cppgm_file_audit.pl --stage pa21 --paths dev/src` after the
   through report passes.
4. Commit cohesive progress once the through check and file audit pass, then
   verify `git status --short` is empty.

## Final Validation

- `make build`: pass.
- `make test-report-through-pa21`: pass, 1621 / 1621.
- `perl scripts/cppgm_file_audit.pl --stage pa21 --paths dev/src`: pass with
  warnings only.
- Temporary diagnostic sweep over `dev/src`: no PA21 debug markers found; only
  normal `cerrno` includes and the test runner `std::cerr` reset remain.
