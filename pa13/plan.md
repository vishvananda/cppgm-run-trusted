# PA13 Implementation Plan

## Scope

Implement `lowir2cy86` as the PA13 LowIR-to-CY86 adapter.  The tool remains a
backend adapter over LowIR text: it parses one or more LowIR input files,
validates the PA13 structural/type/metadata contract, and emits deterministic
PA9 CY86 source text.  It does not lower C++ source, call reference binaries,
emit native objects, or add a second compiler path.

## Design

- Keep `dev/lowir2cy86.cpp` as command-line glue for `-o <outfile> <srcfile>...`.
- Add a small LowIR implementation under `dev/src/`:
  - a typed LowIR model for top-level declarations/definitions, types,
    metadata, values, blocks, slots, and instructions;
  - a text lexer/parser for the PA13 grammar, including metadata and optional
    debug suffixes;
  - a validator for duplicate symbols, object aliases, function-local names,
    block terminators, target existence, metadata values, call signatures, and
    call-boundary parameter rules;
  - a CY86 emitter that owns symbol spelling, stack layout, startup hooks,
    global data layout, function prologues/epilogues, calls, control flow,
    scalar operations, memory operations, object copy/zeroing, atomics, and the
    simplified exception handler stack used by the PA13 tests.
- Wire new `dev/src/*.cpp` files into `FRONTEND_OBJ_BASENAMES_lowir2cy86` only,
  reusing PA9 CY86 source-language conventions but not the PA9 native emitter.

## Validation Strategy

- During parser/emitter work, use the scoped report:
  `make test-report ACTIVE_TEST_REPORT_PAS='pa13'`.
- After meaningful parser, validation, lowering, or shared infrastructure
  changes, run the required through check:
  `make test-report-through-pa13`.
- Before handoff, also run:
  `perl scripts/cppgm_file_audit.pl --stage pa13 --paths dev/src`.
- Keep older-assignment regressions as blockers and leave the worktree clean
  with cohesive progress committed.
