# PA28 Audit

## Audit Plan

- Recheck the PA28 contract against the implementation files that own the
  stage: `dev/lowir2native.cpp`, `dev/src/lowir2native_support.cpp`,
  `dev/src/lowir2native_native.cpp`, `dev/src/lowir2native_mir_helpers.*`,
  `dev/src/lowir2native_mir_opnames.cpp`, and the
  `dev/src/lowir2native_mir_dumper*` split.
- Inspect the shared files changed for PA28 compatibility:
  `dev/src/lowir2cy86*.{h,cpp}`, `dev/src/cy86_model.cpp`,
  `dev/src/cy86_x86.cpp`, and `dev/frontend_source_sets.mk`. Confirm they
  preserve earlier PA behavior and are not used as hidden PA28 substitute
  backends.
- Check ownership boundaries: PA28 should parse typed LowIR, lower to an owned
  machine-IR representation, dump that MIR, then emit a native executable.
  Facts needed for ABI roles, object sizes, storage, call targets, f80, atomics,
  and globals should come from structured LowIR/backend state rather than
  downstream text recovery.
- Audit for forbidden substitutes: skipped compiler phases, dummy output,
  interpreter/VM/trampoline execution, templated binaries, embedded payloads,
  shelling out to reference tools or host compilers, CY86-as-primary fallback,
  test-name/source-shape gates, timeout workarounds, and file-audit bypasses.
- Review performance-sensitive paths for avoidable repeated whole-program
  walks, quadratic liveness/use scans in hot lowering loops, excessive copying
  of function/block/instruction state, repeated MIR text parsing, and full-suite
  or filesystem scans during compilation.
- Run and inspect the required file audit for PA28-owned source size/function
  size issues under `dev/src`; fix implementation layout problems rather than
  hiding code in unchecked paths.

## Findings

- Found native-side CY86 text repair passes in
  `dev/src/lowir2native_native.cpp`: floating literal rewriting, global
  alignment injection, and narrow indirect-load alias patching. These recovered
  backend facts from formatted CY86 text after LowIR emission, which violated
  the audit rule against downstream stringly semantic recovery.
- Found a dummy MIR fallback in
  `dev/src/lowir2native_mir_dumper_dispatch.cpp`: unhandled instruction kinds
  were emitted as `; unsupported`. That could make an unsupported lowering look
  like a successful MIR dump instead of failing the compilation.
- Found an extra `--dump-native-plan` alias in `dev/lowir2native.cpp` and
  `dev/src/tool_help_text.h`. PA28 only requires `--dump-machine-ir`; the extra
  alias widened the stage surface without assignment contract coverage.
- Inspected the PA28 source set registration in
  `dev/frontend_source_sets.mk`. All PA28 backend source files are registered
  for `lowir2native`; no hidden implementation file or unchecked source path was
  found.
- Inspected for reference-tool use, host-compiler shell-out, interpreter/VM
  execution, trampoline/template executable generation, embedded payloads,
  source/test-name gates, timeout workarounds, and fixture-specific output
  bypasses in the PA28-owned backend files and changed shared files. None were
  found.
- Reviewed performance-sensitive MIR analysis paths. The implementation uses
  repeated per-function scans over blocks and instructions for liveness,
  definitions, stack/home decisions, and call/branch quality decisions, but no
  full-suite walks, filesystem scans, or unbounded global recompilation loops
  occur during compilation. No performance blocker was found for the PA28 input
  scale.

## Changes Made

- Moved native float-literal bit conversion, native global `align16` emission,
  and narrow indirect-load register separation into
  `dev/src/lowir2cy86_emit.cpp` and
  `dev/src/lowir2cy86_emit_helpers.cpp`, where `Type`, `Global`, and
  instruction facts are still structured. The helper source is registered for
  both `lowir2cy86` and `lowir2native`.
- Removed the CY86 text sanitizer/injector functions from
  `dev/src/lowir2native_native.cpp`; the native writer now emits the
  native-safe CY86 handoff directly and invokes `cy86::compile_to_file`
  in-process.
- Removed the non-contract `--dump-native-plan` alias from the
  `lowir2native` driver and help text.
- Replaced the MIR dumper's unsupported-instruction placeholder with a hard
  error, and added explicit no-op simulation for valid jump and atomic-fence
  forms.
- Cleaned misleading indentation in the touched MIR dispatch code so the build
  no longer warns on those blocks.

## Validation

- `make test-report ACTIVE_TEST_REPORT_PAS='pa28'`: passed, 106 / 106 tests.
- `make test-report-through-pa28`: passed, 2527 / 2527 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa28 --paths dev/src`: passed
  with 26 warnings and no fatal issues.
