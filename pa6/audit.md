# PA6 Audit

## Audit Plan

Audit the PA6 implementation against the handout contract, current
`pa6/plan.md`, PA1-PA5 regressions, recent commit `479005d`, and the PA6/course
tests.

Files to inspect:

- `dev/recog.cpp` for command-line handling, per-source error isolation,
  required output shape, and absence of fallback OK/BAD gates.
- `dev/src/recog_support.{h,cpp}` for token conversion, special-token handling,
  mock name lookup predicates, parser ownership, backtracking discipline, and
  expression/declaration ambiguity handling.
- `dev/src/recog_grammar.{h,cpp}` for the generated grammar table surface,
  hidden shortcuts, file-audit size pressure, and unchecked implementation
  fragments.
- `dev/src/posttoken_pipeline.{h,cpp}` and
  `dev/src/preproc_support.{h,cpp}` for shared PA1-PA5 behavior regressions,
  token ownership, source-location preservation, and excessive copying.
- `dev/frontend_source_sets.mk` for correct `recog` source wiring without
  moving implementation outside audited source paths.

Performance risks to check:

- Avoidable quadratic token scans during balanced-token, expression, and
  declarator recognition.
- Repeated full grammar or token-suite walks during speculative parsing.
- Excessive token/vector copying on backtracking or per-source pipeline setup.
- Timeout-style caps or early exits that mask algorithmic problems.

Ownership and semantic boundaries to check:

- Parser state should own/borrow tokens clearly, with semantic facts represented
  by token kinds and predicates instead of downstream string recovery.
- Mock name lookup should be centralized and not duplicated as ad hoc spelling
  checks through grammar code.
- PA6 parsing should reuse the PA1-PA5 preprocessing/posttoken pipeline without
  embedding previous-stage payloads or shelling out to reference/host tools.

File-audit issues to check:

- Run `perl scripts/cppgm_file_audit.pl --stage pa6 --paths dev/src`.
- Inspect large/new parser files for hidden implementation fragments,
  generated-code bypasses, or source moved outside `dev/src`.

## Findings

- Mock name lookup facts were duplicated. `dev/recog.cpp` still carried the
  starter `PA6_Is*Name` helpers, while `dev/src/recog_support.cpp` made separate
  raw character checks for the parser. This was a stringly ownership problem,
  even though it did not currently change test results.
- The recognizer rebuilt the parsed PA6 grammar for every source file and
  `decl-specifier-seq` repeatedly scanned the full grammar map to find the
  non-type specifier rules. These were avoidable hot-path costs in the parser
  setup/specifier loop.
- `close-angle-bracket` accepted `OP_GT`, `ST_RSHIFT_1`, or `ST_RSHIFT_2`
  whenever an angle stack entry existed, without rechecking that the parser was
  still at the bracket depth recorded for the matching `OP_LT`. Operator
  matching already had that depth guard; close matching needed the same guard.
- `dev/recog.cpp` did not verify that the `-o` output file opened before
  writing the required report.
- No skipped compiler phases, dummy/minimal success path, reference-binary
  shell-out, host compiler shell-out, interpreter/VM/trampoline/template-binary
  substitute, embedded earlier-IR payload, test-specific path gate, timeout
  workaround, file-audit bypass, or hidden implementation fragment was found.
  The embedded grammar text in `dev/src/recog_grammar.cpp` matches
  `pa6/pa6.gram`.

## Changes Made

- Removed the unused starter mock-name helpers from `dev/recog.cpp` and added
  the missing output-file open check.
- Centralized parser mock name lookup in `dev/src/recog_support.cpp` with typed
  `MockNameCategory` predicates used by class, enum, namespace, template,
  typedef, type-name, and unqualified-id parsing.
- Cached the parsed PA6 grammar as a process-local immutable object instead of
  rebuilding it for each input source.
- Reserved recognizer token storage during post-token conversion.
- Replaced the repeated full grammar-map scan in `append_no_type_specs` with
  the exact nonterminal and terminal set allowed in a non-type
  `decl-specifier`.
- Added the missing bracket-depth check to `parse_close_angle`, keeping close
  angle recognition consistent with the PA6 same-nesting-level rule.

## Validation

- `diff -u pa6/pa6.gram <extracted dev/src/recog_grammar.cpp grammar>`:
  no output, confirming the embedded grammar matches the handout grammar.
- `make test-pa6`: pass, including 32 PA6 handout tests and 11 PA6 course
  tests.
- `make test-report-through-pa6`: pass, `267 / 267` tests across PA1-PA6.
- `perl scripts/cppgm_file_audit.pl --stage pa6 --paths dev/src`: pass,
  `24 files checked`.
