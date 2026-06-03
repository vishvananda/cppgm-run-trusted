# PA1 Implementation Plan

## Scope

Implement the `pptoken` translation phase 1-3 tokenizer as shared compiler
infrastructure under `dev/src`, with `dev/pptoken.cpp` kept as the command-line
entry point. The stage owns UTF-8 input decoding, universal-character-name
translation, trigraph replacement, line splicing, final newline insertion,
comment-to-whitespace handling, and preprocessing-token classification.

## Design

- Add a `pptoken` module in `dev/src` that exposes `run_pptoken(std::istream&,
  IPPTokenStream&)`.
- Decode input bytes into code points with source locations for diagnostics.
  Skip an initial UTF-8 BOM and reject malformed UTF-8.
- Build a translated code-point stream outside raw string literal bodies:
  universal-character-names are decoded first, then trigraphs, then
  backslash-newline splices are removed. Raw string literal scanning will use
  original code points for the raw body after the opening `R"` or prefixed
  `R"` has been recognized.
- Tokenize greedily from the translated stream, emitting through
  `IPPTokenStream` only. Maintain tokenizer state for start-of-line and
  `#include` header-name context rather than recovering those facts from
  formatted output.
- Keep identifiers, pp-numbers, literals, operators, comments, and header names
  in separate helper functions so later assignments can reuse or replace
  pieces without depending on a monolithic entry tool.

## Audit Work

The current audit failure is an oversized optional ABI scaffold header in
`dev/src`. Reduce it to a lightweight interface because the implementation body
is not owned by PA1 and is not compiled by current tools.

## Validation

- Use focused `pa1` checks during development for fast diffs.
- Run the required root gate: `make test-report-through-pa1`.
- Run the required file audit:
  `perl scripts/cppgm_file_audit.pl --stage pa1 --paths dev/src`.
- Commit cohesive progress and verify `git status --short` is empty before
  handing back.
