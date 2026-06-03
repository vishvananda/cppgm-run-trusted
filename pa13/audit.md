# PA13 Audit

## Audit Plan

- Files to inspect:
  - `dev/lowir2cy86.cpp` for driver behavior, command-line contract, failure
    propagation, and absence of fallback success paths.
  - `dev/src/lowir2cy86.h`, `dev/src/lowir2cy86_model.cpp`,
    `dev/src/lowir2cy86_parser.cpp`, `dev/src/lowir2cy86_validate.cpp`,
    `dev/src/lowir2cy86_emit.cpp`, and `dev/src/lowir2cy86_support.cpp` for the
    LowIR model, parser, validator, CY86 lowering, and support helpers.
  - `dev/frontend_source_sets.mk` for the PA13 source-set wiring and to confirm
    new `dev/src/*.cpp` files are in the `lowir2cy86` tool only.
  - `pa13/tests/spec/` plus any `cppgm.tests/course/pa13/` cases for the
    assignment oracle, with earlier PA report coverage checked by
    `make test-report-through-pa13`.
- Performance risks to audit:
  - Parser token/line handling should make one pass over each source file
    without repeated whole-file reparsing.
  - Validator symbol, temporary, slot, and block checks should use owned maps or
    sets rather than repeated full-program scans on every lookup.
  - Emitter stack layout, LowIR-value resolution, global-data flattening,
    `copyobj`/`zeroinit`, switch lowering, and exception support should avoid
    avoidable quadratic walks or excessive string copying on hot paths.
- Ownership boundaries to audit:
  - The parsed `Program` owns top-level entries, functions, globals,
    metadata, blocks, slots, instructions, and typed values.
  - Validation is responsible for structural/type/metadata facts; the emitter
    should consume those facts and not recover missing semantics from raw source
    text or test names.
  - CY86 symbol spelling, stack layout, helper labels, startup hooks, and
    generated temporaries should be owned by the emitter and kept deterministic.
- File-audit issues to inspect:
  - No PA13 implementation fragments should be hidden outside the checked
    `dev/` and `dev/src/` surface.
  - No generated payloads, copied runtimes, template binaries, reference-tool
    calls, weakened audit checks, file-size bypasses, or test-fixture gates
    should appear in the implementation.
  - `perl scripts/cppgm_file_audit.pl --stage pa13 --paths dev/src` must pass
    after cleanup.

## Findings

- The driver and support bridge run a single parse/validate/emit path for normal
  invocations and batch-harness requests.  No reference binary calls, host
  compiler shells, template binaries, embedded payloads, interpreter/VM
  substitutes, fallback success paths, timeout workarounds, or test-fixture gates
  were found in the PA13 implementation.
- `dev/frontend_source_sets.mk` wires `lowir2cy86_model`,
  `lowir2cy86_parser`, `lowir2cy86_validate`, `lowir2cy86_emit`, and
  `lowir2cy86_support` only into `FRONTEND_OBJ_BASENAMES_lowir2cy86`.  No PA13
  implementation fragments were moved to unchecked paths.
- The LowIR model has a clear owner for parsed program facts, and validation
  builds maps/sets for top-level symbols, aliases, parameters, slots, blocks,
  temporaries, and layouts before the emitter runs.  That avoids downstream
  recovery of most semantic facts from raw text.
- Validation was too permissive for role metadata and indirect-call signature
  metadata.  Global roles were accepted without checking that they were global
  roles, reserved EH/runtime roles were not singleton-checked, and
  `as (...) -> ...` call signatures reused the top-level function metadata
  validator, which allowed symbol metadata such as `role` or `object` where only
  call-boundary metadata belongs.
- Bulk object memory lowering copied and zeroed in 8-byte chunks only.  For a
  legal span whose byte count is not a multiple of eight, `copyobj`,
  `zeroinit`, and direct-object return copying could read or write past the
  requested span.
- Bulk-memory operand validation did not enforce the PA13 ownership boundary.
  `copyobj` source and destination operands and `zeroinit` destinations were
  only checked for being defined, leaving malformed operands for the emitter to
  interpret later.
- Performance review did not find repeated whole-suite walks or avoidable
  whole-program hot-path scans in PA13.  Parser input is lexed once per file,
  validation populates lookup maps/sets, and emitter lookups use those maps.
- The explicit f80 rejection paths were inspected against the current PA13
  checked oracle.  The checked general f80 direct-call/global/arithmetic
  fixtures are negative cases, while f80 conversion fixtures are positive.  This
  audit preserved those oracle-compatible outcomes and did not edit references.

## Changes Made

- Added role-kind and singleton-role validation so function roles and global
  roles are checked on the correct top-level kind and each reserved role can be
  owned by at most one symbol.
- Added a call-signature metadata validator that accepts only call-boundary keys:
  `arity`, `effects`, `unwind`, and `return`.
- Added bulk-memory operand validation for `copyobj` and `zeroinit`.  `copyobj`
  now requires a pointer source or a matching direct object source, and bulk
  destinations must be pointer-valued or an addressable stack slot with enough
  owned storage for the requested span.
- Updated `copyobj`, `zeroinit`, and object-return copy emission to preserve the
  existing qword output for qword-aligned spans and to emit exact 64/32/16/8-bit
  tails for non-qword spans.
- Added this audit file and updated `pa13/plan.md` with Architecture Review and
  Final Architecture Review sections grounded in the actual implementation.

## Validation

- `make test-pa13` passed after the cleanup.
- `make test-report-through-pa13` passed: 764/764 tests and 13/13 stages.
- `perl scripts/cppgm_file_audit.pl --stage pa13 --paths dev/src` exited 0.
  It reported six existing warnings in earlier-stage files
  (`nsinit_internal.h`, `pa12_internal.h`, `nsinit_model.cpp`,
  `nsinit_parser.cpp`, `pa11_model.cpp`, and `pa12_types.cpp`) and no fatal
  file-audit issues.
