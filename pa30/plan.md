# PA30 Implementation Plan

## Scope

Implement `abimangle` as a standalone ABI fact encoder in `dev/`. The tool
reads the normalized fact language from `pa30/tests/abi/*.t`, builds typed fact
records using `dev/src/abi_mangle.h`, and emits Itanium C++ ABI names. PA30
does not modify C++ parsing, semantic analysis, LowIR, object generation, or
runtime behavior for earlier compiler stages.

## Design

- Keep command-line ownership in `dev/abimangle.cpp`.
- Parse facts into explicit type, template-argument, expression, context,
  entity, function, and target records instead of recovering semantics from
  formatted mangled text.
- Resolve `let-*` identifiers through a per-case environment while encoding.
- Encode names, types, template arguments, dependent expressions, local
  contexts, ABI tags, thunks, RTTI/vtable/VTT, construction vtables, and TLS
  wrappers from the typed records.
- Maintain an Itanium substitution table in the encoder. Insert substitutable
  components during normal encoding and reuse standard substitutions such as
  `St`, `Sa`, and namespace/type substitutions where the ABI requires them.
- Treat raw symbol/context facts as already-normalized ABI fragments only at
  the documented fact boundaries.

## Ownership Boundaries

- Implementation files live under `dev/` and `dev/src/`.
- If the encoder grows beyond the existing scaffold, move reusable logic to a
  `dev/src/abi_mangle*.cpp` helper and add it to
  `FRONTEND_OBJ_BASENAMES_abimangle` in `dev/frontend_source_sets.mk`.
- Do not edit PA30 handout tests or reference files except for new optional
  tests under `cppgm.tests/course/pa30/` if needed.

## Validation

1. Build `abimangle` through the PA30 harness.
2. Iterate with scoped diagnostics:
   `make test-report ACTIVE_TEST_REPORT_PAS='pa30'`.
3. After meaningful parser or encoder changes, run
   `make test-report-through-pa30`.
4. Run the file audit:
   `perl scripts/cppgm_file_audit.pl --stage pa30 --paths dev/src`.
5. Commit cohesive implementation checkpoints and leave `git status --short`
   clean when PA30 is complete.
