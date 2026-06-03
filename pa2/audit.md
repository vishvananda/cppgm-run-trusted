# PA2 Audit

## Audit Plan

- Re-read the PA2 assignment contract, `TESTING_AND_REFERENCES.md`,
  `pa2/plan.md`, recent commits, and PA1/PA2 tests to verify the implemented
  behavior is scoped to phases 1-6 plus tokenization of phase 7.
- Inspect changed implementation files: `dev/posttoken.cpp`,
  `dev/src/posttoken_support.cpp`, `dev/src/posttoken_support.h`, and
  `dev/frontend_source_sets.mk`.  Treat `dev/src/pptoken_lib.cpp` and
  `dev/src/pptoken_lib.h` as PA1-owned lexer boundaries and check that PA2
  reuses them without regressing PA1.
- Check for skipped compiler phases, fallback success paths, dummy output,
  interpreter/VM/trampoline/template-binary/embedded-payload substitutes,
  source-shape or fixture-specific gates, and hardcoded reference answers.
- Review semantic ownership: PA1 should own phase 1-3 preprocessing-token
  recognition; PA2 should own post-token classification, literal parsing,
  escape decoding, string literal concatenation, ABI type selection, and
  hexdump emission without downstream recovery of facts that should already be
  represented.
- Review performance risks in hot paths: string concatenation buffering,
  escape/UTF encoding, integer literal parsing, simple-token lookup, and input
  streaming.  Look for avoidable quadratic scans, repeated full-suite walks,
  excessive copying, and hot-path recomputation.
- Review file-audit risks: new `dev/src` files must be listed in the proper
  source set, implementation must stay in checked paths, and there must be no
  hidden fragments, generated payloads, weakened audit checks, or code moved to
  unchecked locations.
- Validate with the required root checks:
  `make test-report-through-pa2` and
  `perl scripts/cppgm_file_audit.pl --stage pa2 --paths dev/src`.

## Findings

- No skipped phase, fallback success path, dummy output path, reference-binary
  shellout, host-compiler dependency, interpreter/VM/trampoline, template
  binary, embedded payload, timeout workaround, source-shape gate, or
  fixture-specific acceptance path was found.  `dev/posttoken.cpp` reads stdin,
  consumes PA1 preprocessing tokens through `pptoken::run_pptoken`, and emits
  PA2 output directly.
- PA1 ownership remains intact.  Phase 1-3 translation and preprocessing-token
  recognition stay in `dev/src/pptoken_lib.cpp`; PA2 classification, literal
  parsing, escape decoding, string concatenation, ABI type selection, and
  hexdump emission stay in `dev/posttoken.cpp` and
  `dev/src/posttoken_support.*`.
- File-audit wiring is correct.  The new checked implementation file
  `dev/src/posttoken_support.cpp` is listed for the `posttoken` tool in
  `dev/frontend_source_sets.mk`, and no implementation was moved to unchecked
  paths.
- One performance cleanup item was found in string literal processing:
  decoded-code-point vectors, joined string-literal sources, concatenated
  code-point buffers, encoded byte buffers, and pending parsed pieces could
  avoid extra reallocations/copies on long adjacent string literal sequences.

## Changes Made

- Added this audit document with the required audit plan, findings, changes,
  and validation sections.
- Updated `pa2/plan.md` with `Architecture Review` and
  `Final Architecture Review` sections grounded in the implemented
  `pptoken_lib`/`posttoken`/`posttoken_support` split.
- Updated `dev/posttoken.cpp` to reserve storage while decoding ordinary and
  raw string bodies, joining concatenated literal sources, concatenating
  code-point vectors, and encoding UTF-8/UTF-16/UTF-32 output bytes.
- Updated `dev/posttoken.cpp` to move parsed string pieces into the pending
  string buffer instead of copying them.

## Validation

- `make test-report-through-pa2` passed: 68/68 tests, PA1 and PA2 stages.
- `perl scripts/cppgm_file_audit.pl --stage pa2 --paths dev/src` passed:
  10 files checked.
