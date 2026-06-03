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
