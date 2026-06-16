# PA38 Audit

## Audit Plan

Target stage: PA38 full-stage audit for `lowir2native -O1` and `-O2`.

Files to inspect:

- `pa38/README.md`, `pa38/plan.md`, `pa38/tests/o1/`, `pa38/tests/o2/`, and
  `pa38/tests/debuginfo/` for the assignment contract and structural oracles.
- Latest PA38 implementation commit touching `dev/lowir2native.cpp`,
  `dev/src/lowir2native.h`, `dev/src/lowir2native_support.cpp`, and the
  `dev/src/lowir2native_mir_dumper*.{h,cpp}` modules.
- Earlier backend support reached by PA38, especially native executable output,
  MIR dumping, call lowering, branch lowering, frame-slot lowering, and preserve
  analysis.

Ownership boundaries:

- Keep implementation work in `dev/` and `dev/src/`; PA38 handout, harness, and
  reference sidecars remain oracle material only.
- Preserve PA28 `-O0` native behavior while adding explicit PA38 `-O1` and
  `-O2` MIR cleanup choices.
- Do not introduce host-compiler/reference-binary fallbacks, interpreters,
  VM/trampoline execution, template binaries, or embedded earlier-IR payloads.
- Keep machine facts represented in the backend analyses/dumper rather than
  recovering semantic intent from brittle emitted strings downstream.

Performance risks to inspect:

- O2 block ordering must avoid repeated whole-function scans in hot paths.
- Use-count, definition, live-across-call, frame-temp, and preserve analyses
  should stay linear or near-linear in function size and avoid avoidable large
  object copying.
- O1 copy coalescing, immediate rematerialization, frame-address folding, and
  branch cleanup must not perform repeated full-suite or full-program walks per
  instruction.
- Debug metadata preservation must not be implemented by duplicating complete
  MIR dumps or by expensive postprocessing of the emitted text.

File-audit issues to inspect:

- Hidden implementation fragments outside audited `dev/src` paths.
- Large compressed or minified source lines, generated payload blobs, checked-in
  executable/object substitutes, or unchecked runtime fragments.
- Test-specific acceptance gates keyed to fixture names, exact source shapes, or
  `.ref` sidecars.
- Weakened audit or harness checks, output truncation, timeout workarounds, or
  dummy/minimal output generation.

## Findings

- No reference-binary invocation, host-compiler shell-out, interpreter/VM loop,
  trampoline/template executable, embedded payload, fixture-name gate,
  source-shape gate, timeout workaround, dummy/minimal output path, hidden
  implementation fragment, or file-audit bypass was found in the PA38-owned
  implementation.
- The command-line handoff and support layer preserve the PA28 `-O0` baseline
  while passing `-O1` and `-O2` into the machine-IR dumper. Invalid options,
  missing output paths, missing inputs, unreadable input, invalid LowIR, and
  unsupported targets still fail through the normal compiler path.
- The PA38 MIR cleanup logic is concentrated in `MirDumper` and uses typed
  LowIR instruction/value metadata, use counts, definitions, ABI metadata, and
  frame analysis. The optimized dump is not produced by rewriting previous MIR
  text or by reading oracle data.
- Performance/ownership blocker found: the first PA38 implementation recovered
  folded-address facts with emitter-time whole-function scans in
  `optimized_addr_temp_feeds_load` and `optimized_literal_store_for_addr`, and
  O2 trace layout did a linear block-name lookup for each jump edge. These were
  avoidable quadratic scans on large functions and put semantic decisions in
  the emitter instead of the analysis prepass.
- Correctness blocker found in the same folded-address path: literal-store
  preemission was not limited to single-use address temps. Reusing one address
  temp for multiple stores could incorrectly reuse the first preemitted literal
  value.
- File audit passes for PA38 with warning-level repository shape findings only.
  The warnings do not identify a PA38 fatal issue, unchecked implementation
  path, or hidden payload.

## Changes Made

- Added analysis-owned caches in `MirDumper` for direct-address load temps and
  single-use direct-address literal stores. Emission now consults those cached
  facts instead of rescanning all blocks for each address instruction.
- Removed the unused `optimized_addr_temp_feeds_load_or_store` helper and the
  linear `block_index_by_name` helper.
- Changed O2 block layout to build one block-name map per function before
  following unconditional jump traces.
- Tightened direct-address literal-store preemission so it only applies to
  single-use direct slot/global address temps. Multi-use address temps keep the
  general safe store path.
- Updated `pa38/plan.md` with `Architecture Review` and
  `Final Architecture Review` sections grounded in the current driver, support
  layer, MIR dumper, native writer, and audit cleanup.

## Validation

- `make -C dev lowir2native`: passed.
- `make test-pa38`: passed, 8 / 8 O1 tests and 10 / 10 O2 tests.
- `make -C pa38 test-debuginfo`: passed, 4 / 4 O1 debuginfo tests and
  4 / 4 O2 debuginfo tests.
- `make test-report-through-pa38`: passed, 3323 / 3323 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa38 --paths dev/src`: passed
  with 30 warning-level findings and no fatal issues.
