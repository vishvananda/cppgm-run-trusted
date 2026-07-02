# PA39 Inception Audit

## Audit Plan

Audit the full PA39 inception path for `cppgm++`, with the primary checkpoint:

```sh
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

Checkpoints to inspect:

- PA1 through PA38 preservation: verify PA39 still runs the earlier assignment
  harnesses through the documented checkpoint ladder rather than bypassing or
  weakening expected results.
- PA39 self-host path: inspect `pptoken-self` through `cppgm++-self`, the
  corresponding `*-inception` targets, and object-level comparison behavior for
  PA39-only success paths or special cases.
- Source ownership: confirm checkpoint membership comes only from
  `dev/frontend_source_sets.mk`, with implementation changes in `dev/` or
  `dev/src/` and no generated source-set scan replacing the fixed source lists.
- Harness ownership: inspect `pa39/Makefile` for fixture gates, skipped checks,
  timeout workarounds, restored-self shortcuts leaking into canonical targets,
  dummy outputs, embedded payloads, copied runtimes, trampolines, or
  template-binary substitutes.
- Reproducibility risks: inspect generated host config dependencies, output
  ordering, symlink and link-output updates, absolute paths, timestamps, host
  compiler configuration drift, and linker nondeterminism.
- `pptoken` inception drift: verify the early `compare-pptoken-inception`
  checkpoint remains fixed before relying on full `cppgm++` inception.
- Reducer coverage: inspect recent commits and new `cppgm.tests/course/paN`
  files to decide whether any bug discovered while reaching inception needed an
  earlier-PA reducer.
- Implementation quality: review changed source files for stringly semantic
  facts, ownership mistakes, avoidable hot-path recomputation, excessive
  copying, and performance blockers that could make self-hosting unreliable.
- File audit: run the PA39 file audit over `dev/src` and check for large-file
  or source-organization bypasses.

## Findings

- PA1 through PA38 regression coverage remains intact. The PA39 preservation
  ladder routes earlier PA tests through staged checkpoint binaries and the
  root `make test-report-through-pa38` run passed 3461 of 3461 tests.
- No PA39-only compiler success path was found in `dev/` or `dev/src/`.
  Searches for PA39, inception, self-host, reference-binary, skip, payload,
  trampoline, interpreter, VM, and fixture-gate patterns did not show compiler
  implementation branches for PA39. PA39-specific logic is confined to the
  harness, docs, and test-runner/batch plumbing.
- PA39 source ownership is fixed-list based. `pa39/Makefile` includes
  `../dev/frontend_source_sets.mk` and derives checkpoint sources from
  `FRONTEND_OBJ_BASENAMES_*`; it does not scan `dev/src` to decide what to
  build. A mechanical source-set check found every listed source file on disk.
  The only tracked `dev/src/*.cpp` not in a per-tool list is
  `test_runner.cpp`, which is built by PA39's dedicated runner rule.
- The generated host-config reproducibility issue is fixed in the current
  Makefile. `../dev/src/preproc_support.cpp` now depends on
  `$(INCEPTION_BUILTIN_HOST_CONFIG)`, matching `dev/Makefile`, so clean PA39
  self-host builds cannot compile `preproc_support.o` with the fallback empty
  host include table. This directly covers the earlier
  `compare-pptoken-inception` include failure.
- The canonical inception path still compares real artifacts. Each
  `compare-*-inception` target depends on the self and inception binaries and
  byte-compares them with `cmp`. Inception object rules compare rebuilt objects
  against the matching self-host objects when `INCEPTION_COMPARE_OBJECTS=1`.
  The restored-self path is a separate diagnostic target and does not weaken
  the canonical `compare-cppgm++-inception` target.
- No generated source-set scan, embedded payload, dummy output, copied runtime,
  interpreter, VM, trampoline, template binary, reference-binary shell-out, or
  harness skip was found in the canonical PA39 path.
- Reproducibility hazards are controlled in the audited path. Generated host
  configuration is a make dependency for the source that consumes it, missing
  object scheduling does not change final link input order, and link output is
  written through `.tmp` then installed only when bytes change. No timestamp
  source, unstable source scan, or PA39-only linker ordering workaround was
  found in the canonical compare.
- `compare-pptoken-inception` was run before the full compiler compare and
  reported `MATCH pptoken`, so no unresolved `pptoken` inception drift was
  carried into the final `cppgm++` compare.
- Reducer coverage is present for the earlier compiler bugs fixed while
  reaching inception. Recent PA39-enabling changes added reducers under the
  owning `cppgm.tests/course/paN` directories across PA12, PA14, PA15, PA16,
  PA18, PA20 through PA25, PA29, PA31 through PA34, PA36, and PA37. The current
  host-config dependency defect is a PA39 harness dependency issue, not a C++
  semantic/compiler behavior, so no earlier-PA reducer is required for it.
- The file audit passed for PA39 over `dev/src`. It emitted advisory warnings
  about existing decomposition and duplication hot spots, but no file-audit
  failure or bypass was reported.

## Changes Made

- Added this PA39 audit record with the required audit plan, findings, changes,
  and validation evidence.
- Updated `pa39/plan.md` with an `Architecture Review` and
  `Final Architecture Review` grounded in the actual PA39 Makefile,
  source-set, self-host, inception, object-compare, and validation behavior.
- No source changes were required during this audit phase. The PA39 blocker
  verified by the audit, the generated host-config dependency for
  `preproc_support.o`, was already fixed in the current code under review.

## Validation

Passed in this audit run:

```sh
perl scripts/cppgm_file_audit.pl --stage pa39 --paths dev/src
make test-report-through-pa38
make -C pa39 test-through-pa10 CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-pptoken-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

Observed results:

- `cppgm_file_audit.pl`: exit 0, "File audit passed for pa39" with advisory
  warnings only.
- `make test-report-through-pa38`: exit 0, 3461 of 3461 tests passed.
- `make -C pa39 test-through-pa10 ...`: exit 0, PA1 through PA10 staged
  preservation tests passed.
- `make -C pa39 compare-pptoken-inception ...`: exit 0, `MATCH pptoken`.
- `make -C pa39 compare-cppgm++-inception ...`: exit 0, `MATCH cppgm++`.
