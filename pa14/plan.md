# PA14 Implementation Plan

## Compiler Boundary

PA14 will add `cppgm++ --emit-lowir` as the next mode of the existing
frontend. The driver will parse `--emit-lowir -O0 -o <outfile> <src...>` and
call a new `pa14::emit_lowir` API. Earlier `--emit-ast`, `--emit-types`, and
`--emit-semantics` modes stay on their existing PA10-PA12 paths.

The lowering source of truth is the PA12 typed parser state: resolved bindings,
expression types, value categories, overload-selected callees, constants, and
scope-owned declarations. PA14 should not parse PA12's formatted semantic dump.
Where PA12 currently stores only display nodes, the implementation will add
small structured facts at the same semantic construction points and preserve
the old dump text.

## Ownership And File Layout

- Put PA14 public entry points in `dev/src/pa14_lowir.h`, shared internal
  declarations in `dev/src/pa14_lowir_internal.h`, function lowering in
  `dev/src/pa14_lowir.cpp`, and support/program lowering in focused companion
  source files.
- Add the new object basename to the `cppgm++` source set in
  `dev/frontend_source_sets.mk`.
- Reuse PA11 type helpers and PA12 semantic helpers instead of adding a second
  parser or semantic resolver.
- Keep LowIR naming deterministic from semantic ownership: source-owned globals
  and functions in translation-unit/source order, with stable internal names
  for blocks, temporaries, and slots.

## Lowering Design

- Map supported PA12 scalar, enum, pointer, function, reference, and bounded
  array types to PA13 LowIR types.
- Emit namespace-scope global definitions/declarations before function
  definitions, using object metadata from the resolved qualified C++ binding.
- Lower functions into slots plus ordered blocks:
  - parameters become LowIR parameters and addressable slots when needed
  - local scalar/array/reference declarations allocate deterministic slots
  - expressions lower through explicit lvalue-address and rvalue paths
  - assignments, calls, casts, arithmetic, comparisons, logical forms,
    conditionals, comma, subscript, pointer arithmetic, and sizeof use typed
    expression data
  - `if`, loops, `switch`, labels, `break`, and `continue` create structured
    block control flow
- Keep class/object helpers, templates, function-local statics, and richer
  aggregate initialization out of PA14.

## Validation

Use scoped PA14 reports while diagnosing:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa14'
```

After meaningful parser, semantic, lowering, or driver changes, run:

```sh
make test-report-through-pa14
perl scripts/cppgm_file_audit.pl --stage pa14 --paths dev/src
```

Older-assignment regressions from the through report are blockers. Final state
requires the through report and file audit to pass, cohesive commits for the
intended changes, and a clean `git status --short`.
