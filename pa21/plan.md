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

## Architecture Review

The PA21 implementation is centered on `TemplateDeclaration` objects owned by
the parser and indexed by semantic owner scope. Class, alias, variable, and
function templates use typed `TemplateArgument` values for type, value,
template-template, and pack arguments. Partial-specialization matching lives in
`pa12_templates_instances.cpp`, function-template deduction and specialization
materialization live in `pa12_templates_functions.cpp`, and shared argument
completion/dependency helpers live in the focused `pa12_templates_*.cpp` split
listed by `dev/frontend_source_sets.mk`.

Instantiation reuses the ordinary PA12 declaration/parser path by saving parser
state, installing type/value substitutions, reparsing the selected declaration
body, and restoring state afterward. Completed class specializations are cached
under canonical keys derived from typed arguments, while the record itself also
stores PA11 template-instance arguments for downstream LowIR naming and RTTI.
Member function and variable templates remain attached to the owning template
declaration, so lookup, access, constructor resolution, and hidden-friend ADL
use semantic owner links rather than source filenames or test shapes.

The audit found that some dependent qualified/template-id types were represented
only as `TemplateParameter` names with textual suffixes such as `<>` and
`<decltype>`. That worked for passing tests but made later decisions recover
facts from formatted type names. The cleanup adds explicit PA11 dependent
typename metadata and makes pack detection, deducibility, deferred validation,
and partial-specialization matching use those flags and typed active
instantiation arguments.

LowIR lowering receives ordinary semantic bindings and types. Function
specialization symbols and local-static ownership are attached to bindings
during semantic instantiation; LowIR no longer parses a binding name containing
`::` to decide whether a static member definition should be deferred.

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

## Final Architecture Review

The audited implementation now matches the PA21 architecture target: a typed
template declaration/specialization graph feeds the existing PA14-PA20 LowIR
path without dummy output, skipped phases, embedded payloads, or reference-tool
execution. Remaining strings in the template path are presentation names,
diagnostics, ABI/LowIR symbol spelling, or deterministic cache keys derived from
typed semantic values; they are not used to rediscover dependent typename,
specialization owner, or active-instantiation facts.

The specialization-selection work remains intentionally local to the registered
candidate sets for each primary template or variable template. No audit evidence
showed repeated full-suite walks, timeout workarounds, or unchecked helper files.
The PA21 split source files are present in `dev/frontend_source_sets.mk`, and
the required file audit passes.
