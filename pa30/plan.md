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

## Architecture Review

- The implemented PA30 tool keeps the command-line boundary in
  `dev/abimangle.cpp`; it only parses `-o`, opens the output stream, and calls
  `abi_mangle::mangle_fact_files`.
- `dev/src/abi_mangle.h` is the public fact model. The parser in
  `dev/src/abi_mangle.cpp` populates typed records for types, template
  arguments, dependent expressions, contexts, entities, function components,
  and targets before encoding begins.
- Each `AbiFactCase` builds a per-case `Env` for `let-*` definitions. The
  `Mangler` then resolves references through that environment and owns one
  substitution table for one output name.
- Raw ABI fragments are limited to the normalized fact boundaries that carry
  raw context fragments or raw external symbols. Ordinary operator terminals,
  target records, definitions, and entity references are semantic and fail on
  unknown forms.
- The implementation does not invoke reference binaries, host compilers,
  object tools, interpreters, VMs, trampolines, or embedded payloads. PA30 build
  wiring adds only `abi_mangle` to `FRONTEND_OBJ_BASENAMES_abimangle`.
- Performance is bounded by the size of one fact case: environment and
  substitution lookups use maps, type/template/expression keys are built
  recursively from structured facts, and normal tool execution does not scan
  the test suite or earlier stages.

## Final Architecture Review

- The audited implementation remains a standalone ABI name encoder for
  normalized fact files. It does not alter C++ parsing, semantic analysis,
  LowIR, native code generation, object emission, linking, or earlier PA
  behavior.
- Parser hardening removed default-record and raw-terminal fallback success
  paths: unknown multi-token type forms, definitions, context/entity kinds,
  targets, TLS/thunk shape markers, function qualifiers, operator terminals,
  special terminals, duplicate case targets, and direct raw entity references
  now fail with diagnostics.
- Operator encoding now covers the README-listed semantic operator names used
  by this stage, fixes `bit-and` and `deref`, and resolves ambiguous `plus` and
  `minus` from member/non-member shape plus explicit parameter count.
- Standard-template substitutions respect whether a built-in abbreviation
  already includes template arguments, and member-external facts validate all
  boolean semantic fields instead of skipping them.
- The PA30 source remains under the file-audit limit at 1499 lines in
  `dev/src/abi_mangle.cpp`; no hidden implementation files or unchecked paths
  were introduced.

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
