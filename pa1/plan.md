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
- Build a translated code-point stream with trigraph replacement,
  backslash-newline splicing, and final newline insertion, then decode
  syntactically complete universal-character-names through a tokenizer logical
  character view. This preserves the PA1 behavior where trigraph-produced
  backslashes can introduce UCNs, malformed UCN spellings can fall back outside
  literals, and comments/literals can apply their own context rules. Raw string
  literal scanning will use original code points for the raw body after the
  opening `R"` or prefixed `R"` has been recognized.
- Tokenize greedily from the translated stream, emitting through
  `IPPTokenStream` only. Maintain tokenizer state for start-of-line and
  `#include` header-name context rather than recovering those facts from
  formatted output.
- Keep identifiers, pp-numbers, literals, operators, comments, and header names
  in separate helper functions so later assignments can reuse or replace
  pieces without depending on a monolithic entry tool.

## Audit Work

The earlier file-audit failure was an oversized optional ABI scaffold header in
`dev/src`; it has been reduced to a lightweight interface because the
implementation body is not owned by PA1 and is not compiled by current tools.
The PA1 audit then found a tokenizer architecture gap around late UCN decoding
for structural token decisions; the final implementation fixes that in
`dev/src/pptoken_lib.cpp`.

## Validation

- Use focused `pa1` checks during development for fast diffs.
- Run the required root gate: `make test-report-through-pa1`.
- Run the required file audit:
  `perl scripts/cppgm_file_audit.pl --stage pa1 --paths dev/src`.
- Commit cohesive progress and verify `git status --short` is empty before
  handing back.

## Architecture Review

The implemented PA1 surface matches the planned ownership split. `dev/pptoken.cpp`
is only the CLI wrapper: it constructs `DebugPPTokenStream`, calls
`pptoken::run_pptoken(cin, output)`, and turns exceptions into `EXIT_FAILURE`.
Reusable tokenizer behavior lives in `dev/src/pptoken_lib.cpp`, exported through
`dev/src/pptoken_lib.h`, and `dev/frontend_source_sets.mk` links
`pptoken_lib` only into the `pptoken` tool.

The implementation keeps two character views. `SourceChar` preserves decoded
UTF-8 source code points and source positions for diagnostics and raw string
reconstruction. `TextChar` is the translated stream after trigraph replacement,
line splicing, and final newline insertion. Tokenization consumes this stream
through `LogicalChar`, which decodes syntactically complete
universal-character-names at token decision points. This avoids recovering
semantic facts from formatted output while still allowing literal escape parsing
and comment bodies to apply their own context-sensitive rules.

`Tokenizer::HeaderState` owns include header-name context directly:
start-of-line, after `#`/`%:`, and after `include` are tracked as compiler state
across whitespace and comments. Raw strings are recognized from logical prefixes,
then the raw payload after the opening quote is sliced from `SourceChar` so
phase 1/2 transformations inside the raw string are not baked into token data.

## Final Architecture Review

The audit cleanup fixed the one architecture gap found in the tokenizer:
universal-character-names were previously decoded too late for several
token-boundary decisions. Newlines, whitespace, comments, header names,
literal delimiters, pp-numbers, operators, and non-whitespace fallback now use
the logical character view consistently. Malformed `\u` text outside literals is
not over-rejected; literal escapes still reject malformed escape sequences; and
comment bodies use a non-diagnostic logical view so valid UCNs can form newline
or block-comment close structure without treating invalid comment text as a
compiler error.

No wrapper, fixture gate, dummy output path, reference-tool shell-out,
interpreter/VM/trampoline substitute, embedded payload, timeout workaround, or
file-audit bypass was found in the PA1 implementation. The performance shape is
acceptable for PA1: decoding and phase transforms are linear passes over the
input; token scans advance monotonically; raw-string close search is linear in
the raw literal source range; and operator/prefix matching uses small fixed
tables rather than data-dependent full-suite scans.
