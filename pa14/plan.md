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
  definitions, using the resolved binding, language linkage, and deterministic
  LowIR symbol spelling from the qualified C++ owner.
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

## Architecture Review

The implemented PA14 path is a real source-to-LowIR lowering path rooted in the
PA12 parser and semantic model. `cppgm++ --emit-lowir -O0` routes through
`pa14::emit_lowir`, which constructs a `pa12::internal::Parser` for each input,
parses through PA12 semantics, and lowers the resulting semantic tree. Earlier
`--emit-ast`, `--emit-types`, and `--emit-semantics` modes still call the PA10,
PA11, and PA12 entry points directly.

PA12 now carries the structured facts PA14 needs on `Node`: resolved type, value
category, binding, direct-call binding, operator token, literal token text, and
constant value. PA14 still uses the existing PA12 node-label prefixes to choose
which lowering routine to enter, but it does not recover types, bindings,
operators, calls, constants, or language linkage by reparsing the formatted
semantic dump. The lowering source of truth for semantic decisions is the
structured PA12 state.

The PA14 implementation is split into the public API
`dev/src/pa14_lowir.h`, shared declarations in
`dev/src/pa14_lowir_internal.h`, function/statement/expression lowering in
`dev/src/pa14_lowir.cpp`, program/global emission in
`dev/src/pa14_lowir_program.cpp`, and type/symbol/literal helpers in
`dev/src/pa14_lowir_support.cpp`. `dev/frontend_source_sets.mk` registers all
new PA14 objects in the `cppgm++` source set.

The audit found real cleanup blockers in the first implementation:

- `do` statements were parsed by PA12 but fell through to lowering only their
  body once.
- `switch` condition declarations were not lowered before selector emission.
- `continue` inside a switch nested in a loop targeted the switch exit instead
  of the nearest enclosing loop continuation.
- Case collection for an outer switch recursed into nested switch statements.
- Function declarations omitted reference parameter pass metadata.
- Duplicate function declarations could print duplicate LowIR declarations.
- C language linkage was parsed but not represented on bindings or emitted into
  LowIR metadata.
- Operator-function source names containing punctuation could become invalid
  LowIR symbol tokens.

No reference-binary shell-out, host compiler fallback, interpreter/VM,
trampoline, embedded output payload, timeout workaround, fixture-specific gate,
or file-audit bypass was found in the PA14 implementation.

## Final Architecture Review

The final PA14 architecture keeps one semantic owner for PA14 lowering facts:
PA12 bindings, types, value categories, operators, constants, direct-call
targets, and language linkage are attached during parsing/semantic analysis and
then consumed by PA14. PA14 emits LowIR text from those facts with deterministic
symbol, slot, temporary, and block allocation.

Control-flow lowering now has separate break and continue target stacks. Loops
push both targets; switches push only a break target. This preserves C++
continue semantics through nested switch/loop combinations and keeps switch
break handling local to the nearest switch or loop. `do`, `while`, `for`,
`switch`, switch condition declarations, case/default fallthrough, and nested
switches are all lowered through the same block/terminator path.

The LowIR boundary now preserves call-boundary facts needed by later backends:
reference parameters print `ptr [pass=reference]` in function definitions,
declarations, and indirect-call signatures; variadic and C-linkage metadata are
emitted from structured type/binding facts; duplicate declarations are
deduplicated by LowIR symbol; and source symbol components are sanitized before
they become LowIR `@name` tokens.

The implementation remains within the PA14 procedural boundary. It does not add
class helper generation, template instantiation, startup/shutdown hooks, copied
runtimes, or substituted backend artifacts. File-audit warnings reported by the
repository audit are pre-existing structural warnings in earlier shared files;
the required audit command exits successfully and no PA14 code was moved to
unchecked paths.
