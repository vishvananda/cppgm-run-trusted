# PA3 Implementation Plan

## Scope

Implement `ctrlexpr` as the next staged compiler increment.  The tool remains
a stdin-to-stdout filter over a C++ source file: PA1 translation phases 1-3
produce preprocessing tokens, each logical line is evaluated as one
preprocessor controlling expression, and phase 1-3 failures still return
`EXIT_FAILURE`.

## Ownership

- Keep UTF-8 decoding, trigraph handling, line splicing, comments, final
  newline insertion, and preprocessing-token recognition in
  `dev/src/pptoken_lib.cpp`.
- Add a PA3 support module under `dev/src` that consumes `IPPTokenStream`
  events, splits logical lines, performs the PA3 subset of PA2 token
  conversion, and evaluates controlling expressions using typed values.
- Keep `dev/ctrlexpr.cpp` as the command-line entry point only.
- Reuse `posttoken_support` for token and fundamental-type tables.  Do not
  recover semantics from PA2 debug text.
- Link `ctrlexpr` against `pptoken_lib`, `posttoken_support`, and the PA3
  support module through `dev/frontend_source_sets.mk`.

## Design

- Ignore whitespace-sequence preprocessing tokens and finish the current
  expression on each new-line token.  Empty logical lines produce no output.
- Convert tokens directly from preprocessing-token callbacks:
  operators and alternative operator spellings become PA2 simple tokens,
  keywords remain identifier-or-keyword operands for PA3 except where they are
  alternative operators, `true` and `false` are special primary expressions,
  invalid/header/string/user-defined/non-integral tokens make the line
  semantically invalid.
- Interpret integral literals using PA2 C++11 suffix/base candidate rules,
  then promote signed integral literals to `intmax_t` and unsigned literals to
  `uintmax_t`.  Character literals use the same ABI-signedness rules as PA2.
- Parse the grammar with a hand-written top-down parser.  Left-associative
  binary levels are implemented with loops; the conditional operator parses
  recursively and remains right associative.
- Evaluate with typed 64-bit signed/unsigned state.  Usual arithmetic
  conversions are applied at each arithmetic, comparison, and bitwise operator;
  shifts keep the promoted left operand type and reject negative or >=64 shift
  counts only when the shift is evaluated.
- Preserve short-circuit behavior for `&&`, `||`, and `?:`: skipped branches
  are still parsed for grammar and token validity, but runtime-only errors
  such as division by zero or invalid shifts are suppressed.  The conditional
  result type is still determined from both branches.

## Validation

- Use `make test-report ACTIVE_TEST_REPORT_PAS='pa3'` for focused PA3
  diagnosis.
- After semantic/parser changes, run `make test-report-through-pa3` to verify
  PA1 and PA2 remain preserved.
- Finish with:
  - `make test-report-through-pa3`
  - `perl scripts/cppgm_file_audit.pl --stage pa3 --paths dev/src`
  - a cohesive commit and clean `git status --short`.
