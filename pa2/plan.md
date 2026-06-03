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
