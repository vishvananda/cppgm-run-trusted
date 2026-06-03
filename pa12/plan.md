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

## Architecture Review

The implementation matches the planned split. `dev/cppgm++.cpp` only parses
`--emit-semantics`, builds PA12 options from the existing preprocessing options,
and dispatches to `pa12::emit_semantics`. `dev/frontend_source_sets.mk` includes
the PA12 source files in the `cppgm++` source set, so the implementation remains
under the audited `dev/src/` tree.

PA12 state lives in `dev/src/pa12_internal.h` and the cohesive source modules:
`pa12_support.cpp` owns token collection, parser setup, dump traversal, and
multi-translation-unit output; `pa12_decls.cpp`, `pa12_types.cpp`, and
`pa12_statements.cpp` own declarations, declarators, local scopes, and statement
parsing; `pa12_expr*.cpp`, `pa12_model.cpp`, `pa12_names.cpp`, and
`pa12_records.cpp` own expression typing, conversions, overload selection,
lookup, record helpers, and deterministic node construction.

The PA12 parser reuses PA10 token collection and the PA11 `Type`, `Scope`, and
`Binding` model rather than shelling out or reparsing through an alternate
runtime. The PA11 additions are limited to member-pointer types, function cv in
canonical type comparison/spelling, using-declaration alias tracking, and
member-pointer sizing. PA12 references PA11-owned scopes and bindings while the
owning `Parser` keeps the translation unit alive for the entire dump.

Audit cleanup replaced dump-text recovery with typed expression facts. `Expr`
now carries constant-expression state, integer constant values, builtin identity,
and braced-initializer identity. Enum values, array bounds, `sizeof`, const and
constexpr local facts, and `__builtin_constant_p` now flow through typed
semantic fields instead of being recovered from rendered `Node::line` strings or
literal-only shortcuts.

The call path resolves overload sets through `resolve_call_candidate`, and calls
through function pointers or references now apply the same fixed-parameter
conversion checks before printing the call expression. Assignment handling
rejects const, array, and function lvalues and validates compound-assignment
operand categories instead of accepting an unviable conversion as a fallback.
Pointer conversion now preserves cv rules for object-pointer-to-`void*`
conversions, including rejection of `const T*` to unqualified `void*`.

## Final Architecture Review

The final PA12 implementation has no reference-binary, host-compiler, process
execution, fixture-path, timeout, embedded-payload, interpreter, VM, trampoline,
or template-binary dependency in the compiler implementation. Unsupported
constructs fail through semantic errors inside the PA12 parser rather than
producing dummy success output.

Performance risk is bounded by assignment scale. Lookup walks lexical parents
and using-directive graphs with per-lookup visited sets, overload ranking scans
the candidate set once, and semantic output is accumulated as owned `Node`
trees per translation unit. No repeated full-suite walks, timeout gates, or
test-shape branches are used.

File audit passes for PA12. Its warnings were inspected: the PA12 warning is a
declaration-heavy internal parser header, not an implementation-body include or
unchecked fragment, and the duplicate-block warning reflects reuse of the PA11
declarator/specifier structure while keeping the PA12 semantics in normal
audited source files.
