# PA14 Audit

## Audit Plan

Audit target: `pa14 full-stage`.

Implementation files to inspect:

- `dev/cppgm++.cpp` and `dev/frontend_source_sets.mk` for driver routing,
  source-set registration, and earlier-mode preservation.
- PA14 lowering files: `dev/src/pa14_lowir.h`,
  `dev/src/pa14_lowir_internal.h`, `dev/src/pa14_lowir.cpp`,
  `dev/src/pa14_lowir_support.cpp`, and
  `dev/src/pa14_lowir_program.cpp`.
- PA12 semantic changes that PA14 consumes:
  `dev/src/pa12_internal.h`, `dev/src/pa12_decls.cpp`,
  `dev/src/pa12_expr.cpp`, `dev/src/pa12_expr_nodes.cpp`,
  `dev/src/pa12_expr_pointer.cpp`, `dev/src/pa12_expr_semantics.cpp`,
  `dev/src/pa12_model.cpp`, `dev/src/pa12_names.cpp`,
  `dev/src/pa12_statements.cpp`, `dev/src/pa12_support.cpp`, and
  `dev/src/pa12_types.cpp`.
- PA14 local and course tests under `pa14/tests/general/` and
  `cppgm.tests/course/pa14/`, plus recent PA14 commit contents.

Performance risks to inspect:

- Statement/expression lowering paths for repeated whole-function,
  whole-program, or scope-tree scans.
- Name, type, and symbol lookup helpers for avoidable linear searches on hot
  expression paths.
- LowIR text construction for excessive copying, repeated canonicalization, or
  quadratic concatenation.
- Block and temporary allocation for unnecessary recomputation or unstable
  ordering.

Ownership and semantic-boundary risks to inspect:

- PA14 must lower from PA12 structured semantic facts, not from formatted
  semantic-dump strings or reparsed source text.
- Functions, globals, locals, references, arrays, and expression facts should
  have one semantic owner and deterministic LowIR mappings.
- Unsupported PA14 constructs should fail through the real compiler path, not
  through source-shape gates, fixture-specific checks, or fallback success.
- Earlier PA10-PA12 output modes must keep using their existing frontend and
  semantic ownership boundaries.

File-audit and integrity issues to inspect:

- Newly added `dev/src/*.cpp` files must be present in
  `dev/frontend_source_sets.mk`.
- No oversized source/header/function bodies, hidden fragments, unchecked
  implementation paths, copied runtime payloads, embedded expected output, or
  weakened audit scripts.
- No calls to reference binaries, host compilers, interpreters, VMs,
  trampolines, template binaries, or embedded IR payloads in the compiler
  implementation.

## Findings

- `do` statements were parsed by PA12 but PA14 did not have a lowering branch,
  so a `do` loop emitted only one body execution and skipped the loop condition.
- `switch (int x = ...)` reached `emit_rvalue` on a `condition-declaration`
  node and failed instead of lowering the declaration and switching on the
  declared object.
- PA14 used one loop target stack for both loops and switches. A `continue`
  inside a switch nested in a loop incorrectly jumped to the switch end block.
- Outer switch case discovery recursed into nested switch statements, allowing
  inner cases to appear in the outer switch dispatch.
- Function declarations and indirect-call signatures omitted
  `[pass=reference]` for reference parameters even though definitions had the
  metadata.
- Repeated declarations for the same external function emitted duplicate LowIR
  declarations.
- `extern "C"` linkage was consumed by PA12 but not represented on bindings or
  emitted as LowIR metadata.
- Operator-function names such as `operator+` could print punctuation in LowIR
  symbols, producing invalid `@name` tokens.
- No skipped compiler phase, dummy/minimal output path, reference-binary
  shell-out, host compiler fallback, interpreter/VM/trampoline/template-binary
  substitute, embedded expected output, fixture-specific gate, timeout
  workaround, hidden implementation fragment, or file-audit bypass was found.
- The file-audit command exits successfully. It reports existing structural
  warnings in shared earlier-stage files, but no fatal issue and no PA14 bypass.

## Changes Made

- Added PA12 `Binding::language_linkage` and a parser linkage stack so
  `extern "C"` and nested linkage specifications are represented as binding
  facts.
- Emitted LowIR C-linkage metadata and strong binding metadata from PA14
  declarations, definitions, and globals.
- Added a common PA14 parameter printer so reference parameter metadata is used
  consistently in function declarations, definitions, and indirect-call
  signatures.
- Deduplicated emitted function declarations by final LowIR symbol while still
  suppressing declarations for functions defined in the same LowIR unit.
- Split PA14 control-flow targets into separate break and continue stacks.
- Implemented `do` lowering and fixed switch condition-declaration lowering.
- Stopped outer switch case collection at nested switch statements.
- Sanitized source symbol components before printing LowIR symbols, covering
  operator-function punctuation without changing ordinary identifier spelling.
- Added focused PA14 course tests for do-while lowering, switch condition
  declarations, continue inside switch/loop nesting, nested switch case
  ownership, operator symbol sanitization, reference declaration metadata, and
  duplicate C-linkage declaration emission.

## Validation

- `make test-pa14` passed: local PA14 `67/67`, course PA14 `8/8`.
- `make test-report-through-pa14` passed:
  `ALL TESTS PASSED SUCCESSFULLY! (839 / 839)`.
- `perl scripts/cppgm_file_audit.pl --stage pa14 --paths dev/src` exited 0:
  file audit passed for PA14 with 6 warnings. The warnings are the repository's
  existing shared-implementation structure/duplication warnings, not PA14
  hidden code or audit bypasses.
