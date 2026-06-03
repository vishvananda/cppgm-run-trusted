# PA2 Implementation Plan

## Scope

Implement `posttoken` as the next compiler increment over the existing PA1
preprocessing-token lexer.  The PA2 tool remains a stdin-to-stdout filter:
phase 1-3 failures still return `EXIT_FAILURE`, while valid preprocessing
tokens that do not convert to PA2 tokens are emitted as `invalid` and scanning
continues.

## Ownership

- Keep PA1 translation and preprocessing-token recognition in
  `dev/src/pptoken_lib.cpp`.
- Implement PA2 classification and literal decoding in `dev/posttoken.cpp` as
  an `IPPTokenStream` consumer.
- Add `pptoken_lib` to the `posttoken` source set so `posttoken` reuses the
  same lexer as `pptoken`.
- Do not change PA handout tests or reference files.

## Design

- Map identifiers and preprocessing operators/punctuators through the PA2
  simple-token table; emit `#`, `##`, `%:`, `%:%:`, header names, and
  non-whitespace characters as `invalid`.
- Parse `pp-number` text into integer literals, floating literals, and their
  user-defined forms.  Select integer types by C++11 suffix/base rules for the
  Linux x86-64 ABI and emit little-endian hexdumps.  Validate floating grammar
  before using the PA2 starter decode functions for bit-compatible output.
- Decode character and string literal spelling from the PA1 token data.  Decode
  non-raw escape sequences into code points; keep raw string bodies literal.
- Buffer maximal adjacent string and user-defined-string literal sequences.
  Apply PA2 encoding-prefix and ud-suffix combination rules, concatenate code
  points, append the terminating zero code point, encode to the selected ABI
  character type, then emit one literal, user-defined literal, or invalid.
- Flush the pending string buffer before any non-string token and at EOF.

## Validation

- Use focused fixtures and `make test-report ACTIVE_TEST_REPORT_PAS='pa2'` for
  diagnosis while implementing.
- After meaningful parser/classifier/decoder changes, run
  `make test-report-through-pa2` to confirm PA1 remains preserved.
- Finish with:
  - `make test-report-through-pa2`
  - `perl scripts/cppgm_file_audit.pl --stage pa2 --paths dev/src`

## Architecture Review

The implementation matches the intended PA2 ownership split.  `posttoken` is
implemented as a direct `IPPTokenStream` consumer in `dev/posttoken.cpp`, and
`main` delegates phase 1-3 preprocessing-token production to
`pptoken::run_pptoken(cin, output)`.  The PA1 lexer remains in
`dev/src/pptoken_lib.cpp` and is linked into both `pptoken` and `posttoken`
through `dev/frontend_source_sets.mk`.

The PA2-specific support library in `dev/src/posttoken_support.cpp` owns the
simple-token table, fundamental-type names, output formatting, hexdumps, and
the PA2 floating decode helpers.  The `PostTokenStream` implementation owns
post-token classification, invalid-token continuation, integer and floating
literal grammar checks, character/string escape decoding, string literal
concatenation, encoding-prefix and ud-suffix combination checks, ABI-width
encoding, and EOF flushing.

No reference binary, host compiler, interpreter, VM, trampoline, generated
payload, test fixture path, timeout workaround, or alternate success path is
used by the implementation.  The only filesystem-facing change for PA2 is the
source-set entry that links `pptoken_lib` and `posttoken_support` into the
`posttoken` tool.

## Final Architecture Review

The final audited shape remains a staged compiler increment: PA1 produces
preprocessing tokens, PA2 consumes those tokens and emits analyzed tokens or
`invalid` entries without aborting on post-token conversion failures.  String
literal sequences are buffered until a non-string token or EOF, then validated
and emitted once, which keeps phase 6 ownership localized to PA2 instead of
recovering concatenation facts downstream.

The audit cleanup kept the architecture unchanged and tightened the hot string
literal path by reserving decoded-code-point, joined-source, and encoded-byte
storage and by moving parsed string pieces into the pending buffer.  Required
validation after the cleanup passed:
`make test-report-through-pa2` and
`perl scripts/cppgm_file_audit.pl --stage pa2 --paths dev/src`.
