# PA12 Implementation Plan

## Target

Implement `cppgm++ --emit-semantics -o <outfile> <srcfile...>` as the next
increment on top of the existing PA10 syntax parser and PA11 type/scope model.
The PA10 `--emit-ast` and PA11 `--emit-types` paths remain independent and must
continue to pass through checks.

## Design

PA12 will add a dedicated semantic pass under `dev/src/` and a small driver
wiring change in `dev/cppgm++.cpp`.

The PA12 pass owns:

- parsing function bodies into deterministic semantic output
- local/block scope formation during statement parsing
- expression typing and value-category tracking
- limited standard conversion classification and overload ranking
- call resolution for ordinary functions, function references, and function
  pointers
- PA12 semantic dump formatting

The pass reuses PA11's canonical `Type`, `Scope`, `Binding`, lookup, alias, enum,
record, and `describe_type` support instead of creating a parallel type system.
Any new typed facts needed for PA12 should be stored in semantic values or
bindings, not recovered from formatted dump text.

## Scope Boundaries

Implementation changes stay in `dev/` and `dev/src/`. New PA12 source files must
be added to the `cppgm++` source set in `dev/frontend_source_sets.mk`.

PA12 handout directories, tests, and reference files are read-only oracles. No
test-specific gates, hardcoded fixture behavior, harness weakening, or reference
binary calls are part of the implementation.

## Validation

Use the scoped PA12 report for diagnosis:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa12'
```

After meaningful parser, semantic, lowering, or shared infrastructure changes,
run the required through check:

```sh
make test-report-through-pa12
```

Before completion, also run:

```sh
perl scripts/cppgm_file_audit.pl --stage pa12 --paths dev/src
git status --short
```

Completion requires the through check and file audit to pass, intended changes
committed cohesively, and a clean worktree.
