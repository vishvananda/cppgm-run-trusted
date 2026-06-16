# PA38 Implementation Plan

## Design

PA38 extends the existing `lowir2native` backend as the next stage, preserving
the PA28 `-O0` behavior. The command-line parser will record `-O0`, `-O1`, and
`-O2` in `lowir2native::Options`, and `compile_program` will pass that level to
the machine-IR dumper. The native executable path continues to compile the same
validated LowIR program; PA38 cleanup is reflected in the machine-IR emission
path without introducing an interpreter, VM, alternate compiler, or fixture
gate.

The existing backend does not have a separate mutable machine-IR model; machine
IR is produced by `MirDumper` from LowIR plus its register/frame analyses.
Therefore the PA38 ownership boundary is the dumper and its helper analyses:
local rewrites become `MirDumper` emission choices guarded by
`optimization_level >= 1`, while the O2 block layout choice becomes a dumper
block-order pass guarded by `optimization_level >= 2`.

## O1 Work

- Elide unconditional jumps whose target is the next emitted block.
- Elide the unconditional false-edge jump after a conditional branch when the
  false target is the next emitted block; invert the branch when the true target
  is the fallthrough.
- Emit zero tests (`test reg, reg`) for optimized integer truth branches and
  not-branch cleanup.
- Keep direct return and fresh call-result return values in ABI return
  registers instead of shuffling through temporaries.
- Coalesce single-use integer and floating copies by forwarding registers.
- Rematerialize small integer constants into binary operations and call
  arguments where the target instruction supports immediates.
- Fold single-use frame address temporaries into direct frame operands for
  loads/stores and direct `lea` call argument setup.

## O2 Work

- Use the O1 cleanup and additionally choose a printed block order that follows
  unconditional jump traces so likely successors become fallthrough blocks.
- Let existing frame/preserve analysis recompute preserves and stack usage from
  the surviving emitted machine operations; avoid adding fixed callee-save
  requirements for O2-only cleaned paths.

## Architecture Review

- `dev/lowir2native.cpp` owns only command-line parsing, batch handling, help,
  and the `Options::optimization_level` handoff. It accepts `-O0`, `-O1`, and
  `-O2`; unknown options and missing output/input paths still fail before
  compilation.
- `dev/src/lowir2native_support.cpp` remains the single compiler entry point:
  parse all LowIR inputs, validate/layout the typed `lowir2cy86::Program`, then
  produce any requested outputs from that validated program. It does not read
  sidecars, invoke reference tools, or branch on tests.
- PA38 backend cleanup is owned by `MirDumper` in
  `dev/src/lowir2native_mir_dumper*.{h,cpp}`. The dumper performs per-function
  definition/use/liveness/frame analyses before emission, then gates local O1
  cleanup and O2 block-order cleanup on `optimization_level_`.
- The native executable path remains the PA28 in-process executable writer:
  `dev/src/lowir2native_native.cpp` copies the validated LowIR program for the
  scalar global-call rewrite, emits native-safe CY86, and calls
  `cy86::compile_to_file` in process. The PA38 harness validates behavior of
  that executable and validates optimized backend shape through
  `--dump-machine-ir`; no host compiler, reference binary, interpreter, VM,
  trampoline, template executable, or embedded payload path is present.
- Debug metadata is carried as instruction-local suffix text through each PA38
  MIR rewrite rather than by postprocessing a completed dump.
- File ownership stays within `dev/` and `dev/src`; PA38 tests, scripts, and
  sidecars remain oracle material only.

## Final Architecture Review

- The audit found no skipped PA38 compiler phase, fallback success path,
  reference-tool call, host-toolchain call, fixture-name gate, source-shape gate,
  timeout workaround, dummy output path, hidden implementation fragment, or
  file-audit bypass in the PA38 implementation.
- The main audit finding was in performance and ownership of MIR facts: folded
  address-use decisions and O2 jump-trace layout were being recovered through
  emitter-time function scans. Those decisions now live in the existing
  analysis state: direct-address load temps and literal stores are cached during
  `analyze_instruction_features`, and O2 block layout builds one block-name map
  per function.
- The address-folding cleanup also tightened correctness. Literal-store
  preemission is now limited to single-use direct slot/global address temps, so
  a reused address temp cannot accidentally reuse the first literal value for
  later stores.
- O1/O2 cleanup still uses typed LowIR values, instruction kinds, use counts,
  ABI metadata, and frame analysis as the source of truth. The optimized MIR
  dump is not produced by text rewriting an earlier dump, and no downstream
  recovery of semantic facts was added.
- The file audit passes for PA38-owned paths. Remaining audit output is warning
  level and points at longstanding broad repository shape issues rather than a
  fatal PA38 bypass.

## Validation

- First run `make test-report ACTIVE_TEST_REPORT_PAS='pa38'` while iterating on
  PA38 MIR shape.
- After meaningful backend changes, run `make test-report-through-pa38`.
- Run `make -C pa38 test-debuginfo` to check debug metadata preservation.
- Run `perl scripts/cppgm_file_audit.pl --stage pa38 --paths dev/src`.
- Commit cohesive changes and verify `git status --short` is clean.
