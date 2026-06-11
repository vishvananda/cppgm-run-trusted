# PA30 Audit

## Audit Plan

- Review the PA30 assignment contract in `pa30/README.md`, the implementation
  intent in `pa30/plan.md`, the recent PA30 implementation commit, and the
  checked-in ABI fact tests under `pa30/tests/abi/`.
- Inspect ownership boundaries for the PA30 tool: command-line and output
  handling in `dev/abimangle.cpp`, fact data structures and public API in
  `dev/src/abi_mangle.h`, encoder/parser implementation in
  `dev/src/abi_mangle.cpp`, and build wiring in `dev/frontend_source_sets.mk`.
- Check for forbidden substitutes and shortcuts: shelling out to reference
  tools or host compilers, embedded/cached mangled payloads, trampoline or VM
  implementations, dummy/minimal output paths, skipped target forms, raw
  Itanium fragments outside documented `raw` facts, and test-name or
  source-shape acceptance gates.
- Audit semantic representation boundaries: facts should be parsed into typed
  records, identifier references should resolve through a per-case environment,
  ABI tags/local contexts/special names/templates/dependent expressions should
  be represented explicitly, and downstream mangling should not recover
  semantic facts from already-formatted output strings except for documented
  raw symbol/context boundaries.
- Audit performance risks in hot paths: repeated full-environment scans,
  avoidable quadratic substitution lookup, excessive type/expression copying,
  recursive encoding behavior on deeply nested facts, and repeated full-suite
  walks during normal tool execution.
- Audit file-audit boundaries: confirm PA30 implementation remains in checked
  `dev/` and `dev/src/` files, any new `dev/src/*.cpp` is listed in the
  `abimangle` frontend source set, and no hidden implementation fragments,
  generated payloads, weakened checks, or file-size bypasses exist.
- Re-run the required gates after fixes:
  `make test-report-through-pa30` and
  `perl scripts/cppgm_file_audit.pl --stage pa30 --paths dev/src`.

## Findings

- Found fallback success paths in the fact parser: unknown top-level target
  lines could produce a default target, unknown `let-*`/context/entity forms
  could fall through to default records, unknown multi-token type forms could
  ignore trailing words, and duplicate targets in one case silently selected
  the last target.
- Found raw/semantic boundary leaks: `operator-terminal operator-name:*` and
  direct entity references beginning with `_` could bypass the documented raw
  symbol/context facts.
- Found operator encoding gaps against the PA30 README and Itanium table:
  `bit-and` and `deref` used the wrong encodings, `plus` and `minus` were not
  resolved from unary/binary function shape, and several README-listed operator
  names were missing.
- Found parsed semantic facts that were not fully consumed:
  `member-external-address` skipped its function qualifier booleans, and
  `std-template` ignored whether the standard substitution already included
  its template arguments.
- Found a file-audit size risk: `dev/src/abi_mangle.cpp` was already near the
  1500-line source cap, so cleanup had to preserve or reduce the checked source
  footprint while fixing the issues above.
- Did not find reference-binary, host-compiler, object-tool, interpreter, VM,
  trampoline, embedded-payload, fixture-name, timeout, or hidden-path
  substitutes in the PA30 implementation.

## Changes Made

- Hardened `dev/src/abi_mangle.cpp` parsing so unsupported type forms,
  definition kinds, context/entity kinds, target kinds, TLS wrapper markers,
  thunk markers, function qualifiers, duplicate targets, unknown operators, and
  unknown special terminals fail instead of producing default output.
- Restricted raw mangled entity names to explicit raw-symbol/member-external
  fact boundaries and removed the raw `operator-name:` terminal escape.
- Parsed all `member-external-address` boolean fields into the typed fact
  record and honored `standard_substitution_includes_arguments` for
  `std-template` facts.
- Corrected and expanded semantic operator encodings, including shape-aware
  `plus`/`minus`, correct `bit-and`/`deref`, and README-listed new/delete,
  shifts, compound assignments, and comparison spellings.
- Kept the implementation in `dev/` and `dev/src/`, with `abi_mangle` still
  wired through `dev/frontend_source_sets.mk`, and compacted local helper code
  so `dev/src/abi_mangle.cpp` remains below the file-audit source limit.
- Updated `pa30/plan.md` with Architecture Review and Final Architecture
  Review based on the implemented driver, fact model, environment, encoder, raw
  boundaries, performance shape, and file-audit boundary.

## Validation

- `make -C pa30 test` passed: 73/73 PA30 ABI tests.
- `make test-report-through-pa30` passed: 2670/2670 tests and 30/30 stages
  through PA30.
- `perl scripts/cppgm_file_audit.pl --stage pa30 --paths dev/src` passed with
  26 existing warnings and no fatal issues.
- Manual probes confirmed unknown targets, direct raw entity references,
  raw `operator-name:` terminals, and unknown qualifiers now fail; unary
  `operator+`, member binary `operator+`, binary `operator&`, and
  argument-including standard substitutions encode as expected.
