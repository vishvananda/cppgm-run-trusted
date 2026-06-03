# PA6 Implementation Plan

## Compiler Design

`recog` will reuse the PA1-PA5 frontend pipeline to preprocess and convert each
source file to C++ post-tokens. PA6 adds a recognizer layer that translates
those tokens into parser tokens, applies the PA6 special-token rules, and
recognizes the `translation-unit` grammar from `pa6.gram`.

The parser should be a real grammar recognizer, not a test fixture matcher. It
will keep typed token state with spellings and source locations, split
`OP_RSHIFT` into `ST_RSHIFT_1` and `ST_RSHIFT_2`, and use semantic predicates
for the mock name lookup categories required by PA6.

## Ownership Boundaries

- Keep reusable preprocessing and post-token behavior in the existing `dev/src`
  support code.
- Add PA6 parsing infrastructure under `dev/src` and list it for the `recog`
  tool in `dev/frontend_source_sets.mk`.
- Keep `dev/recog.cpp` focused on command-line handling, output file format,
  and per-source OK/BAD reporting.
- Treat `pa6/` as the handout/test harness area; do not modify tests or
  references to hide implementation gaps.

## Validation Plan

1. Use scoped `make test-report ACTIVE_TEST_REPORT_PAS='pa6'` while diagnosing
   PA6 parser failures.
2. After parser or token pipeline changes that affect shared behavior, run
   `make test-report-through-pa6`.
3. Run `perl scripts/cppgm_file_audit.pl --stage pa6 --paths dev/src`.
4. Commit cohesive progress once the through report and file audit are clean,
   then verify `git status --short` is empty.

## Architecture Review

The implemented `recog` tool follows the planned PA1-PA6 frontend layering.
`dev/recog.cpp` owns command-line validation, output-file creation, the required
`recog <N>` and per-source `OK`/`BAD` lines, and per-source exception isolation.
It builds one PA5 preprocessing option set at program entry and delegates all
source recognition to `recog::recognize_source_file`.

`dev/src/preproc_support.{h,cpp}` exposes `preprocess_source_file`, so PA6
reuses the PA5 preprocessor directly instead of duplicating preprocessing.
`dev/src/posttoken_pipeline.{h,cpp}` exposes `collect_posttokens_checked`,
which uses the same post-token conversion logic as the PA2/PA5 text output path
while collecting typed tokens for the recognizer. Invalid post-tokens return
`BAD` for the current source and do not become parser recovery shortcuts.

`dev/src/recog_grammar.cpp` is an audited in-tree copy of `pa6/pa6.gram`;
the embedded lines match the handout grammar. `dev/src/recog_support.cpp`
parses those lines into an immutable process-local grammar once, converts
post-tokens into recognizer tokens, splits `OP_RSHIFT` into `ST_RSHIFT_1` and
`ST_RSHIFT_2`, and appends the existing EOF token as `ST_EOF`. The parser owns
per-source memoization state and borrows the immutable grammar and token vector.

PA6 semantic facts are represented in one parser-side layer. Special terminals
such as `ST_EMPTYSTR`, `ST_ZERO`, `ST_OVERRIDE`, `ST_FINAL`, and `ST_NONPAREN`
are checked through `token_matches`, while mock name lookup is centralized in
typed `MockNameCategory` predicates. Angle-bracket parsing records the bracket
depth where an `OP_LT` opens an angle pair, blocks `>`/`>>` operators only at
that depth, and accepts `close-angle-bracket` only at the matching depth.

## Final Architecture Review

The audit cleanup left the architecture aligned with the PA6 contract. There
are no reference-binary calls, host compiler calls, template binary payloads,
interpreter/VM/trampoline substitutes, test-path gates, dummy success outputs,
or timeout workarounds in the PA6 implementation. The recognizer always runs
the PA5 preprocess and post-token pipeline before parsing; any failure in those
phases produces `BAD` for that source.

Ownership boundaries are now explicit: `dev/recog.cpp` owns only tool I/O,
`preproc_support` and `posttoken_pipeline` own reusable earlier-stage behavior,
`recog_grammar` owns the handout grammar text, and `recog_support` owns token
adaptation, mock lookup, special terminals, angle state, and grammar
recognition. Performance blockers found during audit were fixed by caching the
parsed grammar, reserving recognizer token storage, and replacing a repeated
full grammar-map scan in `decl-specifier-seq` with the exact non-type
specifier set.

Final validation passed:

- `make test-pa6`
- `make test-report-through-pa6`
- `perl scripts/cppgm_file_audit.pl --stage pa6 --paths dev/src`
