# PA37 Audit

## Audit Plan

- Implementation files to inspect: `dev/lowiropt.cpp`,
  `dev/src/lowiropt.h`, `dev/src/lowiropt_program.cpp`,
  `dev/src/lowiropt_canonical.cpp`, `dev/src/lowiropt_simplify.cpp`,
  `dev/src/lowiropt_inline.cpp`, `dev/src/lowiropt_slots.cpp`,
  `dev/src/lowir2cy86.h`, `dev/src/lowir2cy86_parser.cpp`,
  `dev/cppgm++.cpp`, `dev/src/pa29_toolchain.cpp`,
  `dev/src/pa14_lowir.cpp`, `dev/src/pa14_lowir_program.cpp`,
  `dev/src/pa14_lowir_object_init.cpp`, `dev/src/pa12_records.cpp`,
  and `dev/include/cstdio`.
- Build ownership boundaries: keep command-line parsing in `dev/lowiropt.cpp`,
  keep reusable optimizer entry points in `dev/src/lowiropt_*`, keep source
  driver and native backend integration in existing driver/toolchain files, and
  avoid moving optimizer fragments outside `dev/src` or into unchecked PA
  harness paths.
- Correctness risks to inspect: `-O0` must be parse/dump only; `-O1` and
  `-O2` must route through the real LowIR model without fallback success paths,
  host compiler shell-outs, interpreters, VMs, trampoline payloads, templated
  binaries, embedded earlier-IR payloads, source-shape gates, or skipped phases.
- Semantic risks to inspect: executable-edge propagation, EH block and handler
  preservation, inlining inside EH regions, readnone call DCE, slot traffic
  cleanup, scalar and pointer slot promotion, debug metadata preservation, and
  driver `--emit-lowir`, compile, and link optimization-level plumbing.
- Performance risks to inspect: repeated whole-program scans inside function
  fixed points, avoidable quadratic block/instruction walks, excessive copying
  of LowIR instructions or function bodies, recomputation of type/use maps on
  hot paths, and test-suite or filesystem scans from compiler execution.
- Representation risks to inspect: stringly semantic facts, duplicated temp or
  slot ownership, downstream recovery of facts from dumped text, stale CFG/use
  caches after mutation, and synthetic names that could collide with user LowIR
  names.
- File-audit risks to inspect: hidden implementation in unchecked directories,
  oversized or compressed source fragments, generated/runtime payload copying,
  weakened source-set coverage, and any bypass of
  `scripts/cppgm_file_audit.pl --stage pa37 --paths dev/src`.

## Findings

- The optimizer was real LowIR model code, not a reference shell-out,
  interpreter, VM, trampoline, template-binary, copied runtime, or embedded
  earlier-IR payload substitute. The hidden `--batch-stdin` path is shared test
  worker plumbing and still routes through the same compiler implementation.
- `lowiropt` parsed and transformed LowIR but did not validate input or output
  fragments semantically. Invalid LowIR with an undefined block target could be
  accepted by the optimizer path instead of failing at the PA37 boundary.
- The O1 and O2 fixed-point drivers used fixed 20-pass caps. That was a
  timeout-style guard rather than a real fixed point. Removing it exposed two
  concrete issues: O1 reported progress for recorded facts even when no IR
  changed, and the inliner required repeated full-program walks for large
  hosted STL-shaped LowIR.
- Clearing validator-owned caches before validation exposed an older ownership
  bug in PA31 host-object emission: object-only translation units had relied on
  stale or fabricated executable entry state before calling the executable
  layout validator.
- Multi-block single-return inlining only rewrote the original block suffix.
  After O1 slot promotion, a call result can also have dominated uses in other
  blocks, including EH cleanup blocks, so those uses needed whole-caller
  replacement.
- File audit passed. The 30 warnings are existing broad-ownership,
  duplication, and large-literal warnings outside the PA37 optimizer cleanup;
  no new unchecked source path, file-size bypass, hidden implementation
  fragment, or weakened audit coverage was found.

## Changes Made

- Added LowIR fragment validation through `lowir2cy86::validate_fragment` and
  wired `lowir2cy86_validate` into the `lowiropt` source set so `lowiropt`
  validates parsed input and optimized output without requiring an executable
  entry function.
- Added `validate_and_layout_fragment_allow_f80` for host object emission and
  changed PA31 object writing to use that fragment layout path instead of
  fabricating entry state before executable validation.
- Made validator collection clear cached top-level, function-local, role, temp,
  slot, layout, and EH-runtime state before rebuilding facts.
- Replaced fixed O1/O2 pass caps with true convergence. O1 now reports a
  changed pass only when the IR is actually mutated, not merely when a fact is
  recorded for possible propagation.
- Batched O1 inlining within the first active inline-priority tier to avoid
  repeated full-program walks on large LowIR while preserving the existing
  priority order visible in PA37 output references.
- Fixed multi-block single-return inlining to replace the call result
  throughout the caller when the original call result has uses outside the
  immediate suffix.
- Added a course regression test for invalid LowIR with an undefined branch
  target:
  `cppgm.tests/course/pa37/o1/200-invalid-undefined-block-target.t`.

## Validation

- `make test-pa37` passed.
- `CPPGM_SKIP_DEV_REBUILD=1 make -C pa36 check TEST=tests/link/600-hosted-unordered-set-pointer-link-smoke.t`
  passed after the inliner/convergence cleanup.
- `make test-report-through-pa37` passed:
  `ALL TESTS PASSED SUCCESSFULLY! (3305 / 3305)`.
- `perl scripts/cppgm_file_audit.pl --stage pa37 --paths dev/src` passed with
  30 warnings and exit status 0.
