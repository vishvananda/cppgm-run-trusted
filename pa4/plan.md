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

## Architecture Review

The implemented PA4 stage matches the planned in-process pipeline.  `macro`
is a thin CLI wrapper over `macro::run_macro`; `pp_token` owns collection,
replay, and token predicates for phase-3 preprocessing tokens; `macro_support`
owns directive parsing, macro table state, argument substitution, blue-paint
unavailable-name state, stringization, and token pasting; and
`posttoken_pipeline` owns the PA2 conversion shared by `posttoken` and
`macro`.

No reference binary, host compiler, interpreter, VM, trampoline, template
binary, embedded payload, fixture path, or timeout-based success path is used
by the PA4 implementation.  `macro_support` consumes the PA1 tokenizer and
the PA2 posttoken emitter directly.  The PA4 source-set entry lists
`pptoken_lib`, `pp_token`, `posttoken_support`, `posttoken_pipeline`, and
`macro_support`, so the new implementation is compiled into the tool rather
than hidden behind unchecked includes or generated fragments.

The main architecture risk was blue-paint ownership around function-like
replacement tokens and `##` retokenization.  Function-like replacement-list
tokens intentionally do not inherit every unavailable name from the macro
head, because PA4's course-defined parameter and helper-call rules require
some helper macros to remain callable on rescan.  The implementation now
preserves unavailable names on pasted tokens by unioning the paste operands'
paint, and separately marks reconstructed identifiers that match unavailable
macro names on the head.  Object-like names block immediately; function-like
names block only when the call is formed in the replacement context.  This
keeps recursive object-like reconstructions finite without breaking helper
tail-call rescans such as `FILLER_0`/`FILLER_1`.

## Final Architecture Review

After audit cleanup, the architecture remains cohesive and stage-local.
Whitespace and newline facts are retained in `PPToken` until directive parsing,
argument collection, stringization, replacement comparison, and posttoken
emission no longer need them.  Macro definitions use typed fields for
function/object kind, variadic state, parameter indexes, and normalized
replacement tokens; downstream code does not recover macro facts from raw
strings or fixture names.

The remaining vector-based rescanning uses local text sequences and macro
replacement lists, not full-suite or file-wide repeated walks.  The audited
blocker was not a timeout workaround but an actual nontermination risk caused
by lost unavailable-name paint during nested function-like replacement and
token pasting; that state is now represented on the generated tokens.  File
audit passes with all implementation under `dev/src` and no hidden
implementation fragments.
