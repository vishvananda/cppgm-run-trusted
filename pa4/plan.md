# PA4 Implementation Plan

## Scope

Implement `macro` as the next frontend stage over the existing PA1/PA2 code:
read source through `pptoken::run_pptoken`, parse PA4 `#define` and `#undef`
directives, macro-expand text sequences, then emit the expanded preprocessing
tokens through the PA2 posttoken conversion.

## Design

- Add shared token plumbing in `dev/src` for collecting and replaying
  preprocessing tokens, including whitespace/new-line tokens needed for
  directive recognition and macro argument/stringization semantics.
- Factor the PA2 posttoken emission into a reusable function so `posttoken`
  and `macro` share literal, keyword, operator, and string-concatenation
  behavior.
- Represent macros with typed state: object/function kind, parameter list,
  variadic flag, and a canonical replacement-list token sequence.  Redefinition
  checks compare macro kind, parameters, variadic state, and normalized
  replacement tokens including meaningful whitespace positions.
- Parse directives only from phase-3 token positions that start a line after
  optional whitespace.  Macro-produced `#` tokens remain ordinary text tokens.
- Expand text sequences by rescanning token lists.  Identifier tokens carry a
  per-token unavailable macro-name set for blue-paint recursion handling.
- For function-like macros, collect raw arguments before expansion; use raw
  arguments for stringization and `##`, expanded arguments for ordinary
  parameter substitution, and keep argument token paint across substitution.
- Implement `##` by concatenating neighboring raw spellings, retokenizing the
  pasted spelling with the PA1 tokenizer, and rescanning the resulting token(s).
  Empty arguments act as placemarkers and are removed.

## Validation

- Use `make test-report ACTIVE_TEST_REPORT_PAS='pa4'` while diagnosing PA4.
- After meaningful implementation checkpoints, run
  `make test-report-through-pa4`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa4 --paths dev/src`.
- Before completion, commit cohesive changes and verify `git status --short`
  is empty.
