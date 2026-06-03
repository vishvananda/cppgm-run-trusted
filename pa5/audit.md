# PA5 Audit

## Audit Plan

Files to inspect:

- `dev/preproc.cpp`
- `dev/src/preproc_support.cpp`
- `dev/src/preproc_support.h`
- `dev/src/macro_support.cpp`
- `dev/src/macro_support.h`
- `dev/src/ctrlexpr_support.cpp`
- `dev/src/ctrlexpr_support.h`
- `dev/src/posttoken_pipeline.cpp`
- `dev/src/posttoken_pipeline.h`
- `dev/src/posttoken_support.cpp`
- `dev/src/posttoken_support.h`
- `dev/src/pptoken_lib.cpp`
- `dev/src/pp_token.cpp`
- `dev/src/pp_token.h`
- `dev/src/IPPTokenStream.h`
- `dev/frontend_source_sets.mk`
- PA5 and course PA5 tests under `pa5/tests/` and `cppgm.tests/course/pa5/`

Ownership boundaries to verify:

- `pptoken_lib` owns phase 1 through 3 token production and source location
  tagging without PA5-only tokenization forks.
- `macro_support` owns macro parsing, replacement, predefined macro hooks,
  argument handling, stringizing, token paste, and unavailable-name state.
- `ctrlexpr_support` owns typed PA3 controlling-expression evaluation used by
  PA5 `#if` and `#elif`.
- `preproc_support` owns PA5 directive orchestration, include resolution,
  conditional stack state, `_Pragma`, `#line`, `#pragma once`, and final token
  collection.
- `dev/preproc.cpp` remains a command-line and output wrapper.

Performance risks to inspect:

- Repeated full macro-table or token-stream scans on each directive.
- Quadratic copying during macro expansion, include processing, `_Pragma`
  removal, or output assembly.
- Repeated filesystem probing for pragma-onced includes without retaining the
  required file-id state.
- Hot-path string reconstruction of source facts that should be represented in
  token/source state.

File-audit issues to inspect:

- PA5 implementation must stay in `dev/` and `dev/src/`.
- New source files must be listed in `dev/frontend_source_sets.mk`.
- No implementation fragments should be hidden in PA directories, generated
  fixtures, scripts, unchecked paths, or embedded payloads.
- The file audit must pass with
  `perl scripts/cppgm_file_audit.pl --stage pa5 --paths dev/src`.

Shortcut and regression checks:

- No skipped compiler phase, fallback success path, dummy output, interpreter,
  VM, trampoline, templated binary, copied runtime, embedded earlier-IR payload,
  host compiler shell-out, test-specific gate, timeout workaround, or reference
  binary dependency.
- Earlier PA1 through PA4 tools must continue to use the shared implementation
  and pass the through-PA5 report suite.

## Findings

- No regression blocker was found against PA1 through PA4 behavior in the
  audited through-PA5 implementation. `make test-report-through-pa5` exercises
  all tracked stages through PA5 and passes.
- No skipped compiler phase, dummy output path, fallback success path,
  interpreter/VM/trampoline/template-binary substitute, embedded payload,
  host compiler shell-out, reference-binary dependency, test-specific gate, or
  timeout workaround was found in the PA5 source path.
- Ownership is aligned with the plan: `preproc_support` owns PA5 directive and
  include orchestration; `macro_support`, `ctrlexpr_support`, `pptoken_lib`,
  `pp_token`, and `posttoken_pipeline` retain their earlier-stage shared
  responsibilities.
- File-audit boundaries are intact. The new PA5 source file is in `dev/src`,
  is registered in `dev/frontend_source_sets.mk` for `preproc`, and no PA5
  implementation was found in handout, fixture, script, or unchecked paths.
- Cleanup issue found and fixed: `Preprocessor` retained an unused copy of
  `Options`, the PA5 file-id syscall scratch struct was not initialized before
  failed probes, and local directive/pragma token copies did not reserve known
  capacity.
- No unresolved architecture, performance, ownership, file-audit, cheating, or
  regression blocker remains from this audit.

## Changes Made

- Added this audit document with the required plan, findings, changes, and
  validation sections.
- Updated `pa5/plan.md` with `Architecture Review` and
  `Final Architecture Review` sections grounded in the current implementation.
- Cleaned `dev/src/preproc_support.cpp` by removing unused retained options
  state, initializing file-id scratch storage, and reserving vector capacity
  for known-size token copies in directive slicing and `_Pragma` removal.

## Validation

- `make test-pa5` passed: PA5 local tests passed 62/62 and course PA5 tests
  passed 6/6.
- `make test-report-through-pa5` passed: all tracked stages through PA5 passed
  224/224 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa5 --paths dev/src` passed:
  20 files checked.
