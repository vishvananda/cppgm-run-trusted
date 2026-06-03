# PA9 Audit

## Audit Plan

Target: PA9 full-stage `cy86`.

Files to inspect:

- `dev/cy86.cpp`: command-line handling and compile entry point, including `-o`,
  input ordering, and optional target handling.
- `dev/frontend_source_sets.mk`: PA9 source-set wiring for `cy86`.
- `dev/src/cy86_model.h` and `dev/src/cy86_model.cpp`: typed CY86 model,
  opcode/register descriptors, literal conversion, and operand metadata.
- `dev/src/cy86_parser.cpp`: PA5 preprocessing/post-token conversion,
  translation-unit concatenation, grammar recognition, and preservation of
  literal/register/label facts.
- `dev/src/cy86_support.cpp`: compile-to-file orchestration and output file
  permissions.
- `dev/src/cy86_x86.h` and `dev/src/cy86_x86.cpp`: semantic validation,
  label layout, x86-64 lowering, data emission, floating-point handling,
  syscall lowering, and ELF construction.
- `pa9/tests/` and `cppgm.tests/course/pa9/`: coverage for valid programs,
  ill-formed input, multi-translation-unit ordering, data/literal layout, and
  runtime behavior.

Ownership boundaries to verify:

- Parser owns only token grammar and source-order statement construction.
- Model owns semantic facts such as opcode/register descriptors, operand forms,
  widths, literal signedness, and byte conversion.
- Lowering owns validation, layout, relocatable label resolution, machine-code
  emission, and ELF image assembly.
- Support/CLI owns file IO and orchestration only; it must not contain semantic
  shortcuts.

Audit risks:

- Regression against PA1-PA8 preprocessing/token behavior when CY86 reuses the
  PA5 pipeline.
- Skipped validation or fallback success for ill-formed CY86 programs.
- Dummy output, empty ELF generation, embedded payloads, interpreters, VMs,
  trampolines, copied runtimes, or templated binaries instead of real emitted
  machine-code artifacts.
- Test-specific gates based on filenames, source shapes, fixture text, stdout
  expectations, or hardcoded answers.
- Timeout workarounds instead of bounded parser, layout, and emission logic.
- Stringly semantic facts or duplicated ownership that require downstream
  recovery of opcode/register/literal semantics.
- Avoidable quadratic scans, repeated full-program passes inside hot paths,
  excessive byte-vector copying, or repeated descriptor lookup during emission.
- File-audit problems: oversized files, hidden implementation fragments outside
  `dev/src`, source-set omissions, weakened audit checks, or moved code in
  unchecked paths.

## Findings

- **String literal statement alignment was incorrect.**  `cy86_x86` aligned
  literal statements by encoded byte length, so a string literal after `data8`
  was padded to the full string size.  Reference probes showed `"abc"` should be
  placed one byte after the preceding `data8`, not four bytes after it; wide
  string literals showed the same byte-alignment rule.
- **Memory literal address validation was too strict.**  The lowerer rejected
  bare floating literals and register-plus-floating-literal addends in memory
  addresses.  The PA9 memory rule interprets those literal terms as 64-bit
  immediate values.  Label addends remain integral-only because the README
  explicitly requires that for label-plus/minus-literal forms.
- **Lowerer cleanup found no-op audit noise.**  The 80-bit operand validation
  had a helper that always returned true for every operand kind, and the float
  conversion path had leftover locals/string parsing clutter.  These were not
  behavioral blockers, but they weakened audit readability.
- **No cheating/fallback blockers found.**  The PA9 path emits ELF and x86-64
  bytes directly from parsed CY86 statements.  The audit did not find reference
  binary calls, host compiler shell-outs, embedded program payloads,
  interpreter/VM/trampoline substitutes, fixture-name gates, timeout
  workarounds, or file-audit bypasses in PA9 implementation files.
- **No PA9 performance blockers found.**  Parser work is linear in post-tokens,
  layout/emission is linear in statements with fixed-size instruction emission,
  and descriptor lookup is a small bounded table scan.  No repeated full-suite
  walk or avoidable hot-path quadratic behavior was found.

## Changes Made

- Added `LiteralValue::alignment` in `cy86_model` so literal alignment is an
  explicit typed fact.  Scalar literals use their fundamental type size; string
  literal arrays use byte alignment.
- Changed PA9 data layout to use `LiteralValue::alignment` instead of encoded
  byte length for literal statements.
- Relaxed memory-address validation for non-label literal address terms so
  they are converted as 64-bit immediates; preserved integral validation for
  label addends.
- Removed the no-op 80-bit operand helper and leftover float-conversion locals
  from `cy86_x86`.
- Added course regressions:
  `cppgm.tests/course/pa9/010-string-literal-alignment.t.1` and
  `cppgm.tests/course/pa9/011-wide-string-literal-alignment.t.1`, with
  reference sidecars generated by `cy86-ref`.

## Validation

- Focused PA9 course regression check:
  `perl pa9/scripts/run_all_tests.pl ./dev/cy86 my cppgm.tests/course/pa9`
  and `perl pa9/scripts/compare_results.pl ref my cppgm.tests/course/pa9`
  passed for `2/2` tests.
- Targeted reference probes matched for ordinary string, `u` string, and `U`
  string literal label alignment, and for bare/register-addend floating memory
  address terms.  Non-integral label addends remain rejected per the README.
- Required through-stage report:
  `make test-report-through-pa9` passed with `355 / 355` tests and all PA1-PA9
  stages passing.
- Required file audit:
  `perl scripts/cppgm_file_audit.pl --stage pa9 --paths dev/src` passed.  It
  reported three existing warnings in PA8-era `nsinit`/`nsdecl` files and no
  PA9 source blockers.
