# PA28 Implementation Plan

## Scope

PA28 adds the `lowir2native` backend for the existing compiler. The input
surface is the PA13 LowIR model already used by PA14-PA27, and the output is a
Linux x86-64 executable plus an optional deterministic machine-IR dump.

Implementation changes live in `dev/` and `dev/src/`. The `pa28/` directory is
only the assignment contract, harness, and oracle data.

## Design

- Reuse the typed PA13 LowIR parser, validator, role resolution, and layout
  code as the source of semantic facts. Do not recover types, ABI roles, or
  object sizes from formatted output text.
- Add a PA28-owned machine-IR layer that represents native operations,
  registers, stack homes, globals, startup calls, direct/indirect calls,
  compare-fed branches, object copies/zeroing, floating operations,
  conversions, and atomics.
- Lower LowIR directly into that machine IR. Direct LowIR calls and branches
  remain direct machine-IR operations; truly indirect calls remain indirect;
  structured globals remain machine-IR global data items.
- Use the existing PA9 native instruction/container knowledge only as the final
  x86-64 executable emission layer. The primary backend boundary for PA28 is
  LowIR to machine IR, and `--dump-machine-ir` serializes that same lowered
  program.
- Keep the first implementation conservative: stack homes may be used where
  pressure or ABI boundaries require them, while the MIR lowering still exposes
  the direct operation families required by the strict and structural PA28
  oracles.

## Architecture Review

- The current `lowir2native` driver parses PA28 command-line forms in
  `dev/lowir2native.cpp`, builds `lowir2native::Options`, and delegates all
  compiler work to `dev/src/lowir2native_support.cpp`. The driver now exposes
  only the PA28 contract surface for MIR dumping: `--dump-machine-ir`.
- `lowir2native_support.cpp` parses all LowIR sources through the shared
  PA13/LowIR model in `lowir2cy86::parse_files`, then runs
  `validate_and_layout_allow_f80`. That preserves typed facts for values,
  slots, globals, call signatures, metadata, f80 storage, and stack layout
  before either output path runs.
- `--dump-machine-ir` is owned by `MirDumper` and helper modules under
  `dev/src/lowir2native_mir_dumper*` plus
  `dev/src/lowir2native_mir_helpers.*`. The dumper works from the typed
  `lowir2cy86::Program` object, performs per-function definition/use/liveness
  analysis, and emits direct machine-IR operations for startup calls, globals,
  scalar/floating operations, branches, direct and indirect calls, bulk memory,
  f80, atomics, and ABI/frame metadata. Unsupported instruction kinds now fail
  instead of producing placeholder MIR.
- Native executable writing is in `dev/src/lowir2native_native.cpp`. It makes a
  native-owned copy of the validated LowIR program for the scalar-pointer global
  call-target rewrite, emits native-safe CY86 through
  `lowir2cy86::emit_cy86_for_native`, and invokes the existing PA9 CY86 ELF
  writer in-process through `cy86::compile_to_file`. No reference binaries,
  host compilers, subprocesses, interpreters, VM loops, runtime payloads, or
  template executables are used.
- The CY86 handoff remains the executable container/emission bridge, but the
  audit removed the native-side text repair passes. Floating literal bit
  materialization, native global alignment, and narrow indirect-load register
  safety now happen in `lowir2cy86_emit.cpp` and
  `lowir2cy86_emit_helpers.cpp` from typed `Type`, `Global`, and instruction
  data before CY86 parsing.

## Ownership Boundaries

- `dev/lowir2native.cpp` owns command-line parsing, batch handling, and calls
  into the backend.
- New reusable PA28 backend files under `dev/src/` own machine-IR data,
  LowIR-to-machine lowering, MIR dumping, and executable writing. Any new
  source file must be registered for `lowir2native` in
  `dev/frontend_source_sets.mk`.
- PA13 LowIR support may be extended only for shared semantic facts needed by
  both backends. Existing PA1-PA27 behavior must remain unchanged.
- PA28 tests, refs, scripts, grammar, and harness files are not implementation
  targets.

## Final Architecture Review

- The PA28 stage now has a clear owned boundary for tested backend shape:
  validated LowIR is lowered by `MirDumper` into deterministic x86-64 machine
  IR, and every in-scope PA28 instruction either emits/simulates explicit MIR
  or fails compilation. The previous catch-all `; unsupported` MIR row is gone.
- The executable path still reuses the PA9 CY86-to-ELF implementation as the
  final native image writer, but no longer depends on downstream text scanning
  to recover float, alignment, or narrow-load facts. Those facts are represented
  while the LowIR `Program` is still typed and are emitted directly by the
  native CY86 handoff.
- Source ownership matches the intended split: the driver is small, PA28 MIR
  behavior is in responsibility-named dumper modules, shared LowIR parsing and
  validation extensions stay in the `lowir2cy86` model/parser/validator, and
  `dev/frontend_source_sets.mk` registers every PA28 backend source used by
  `lowir2native`.
- The audit found no test-name gates, source-path gates, fixture-specific
  output bypasses, timeout workarounds, reference-tool calls, host-compiler
  calls, copied runtime payloads, or file-audit bypasses in the PA28
  implementation.

## Validation

- Use `make test-report ACTIVE_TEST_REPORT_PAS='pa28'` for fast PA28 diagnosis.
- After meaningful backend or shared LowIR changes, run
  `make test-report-through-pa28`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa28 --paths dev/src`.
- Commit cohesive progress after stable checkpoints and finish with
  `git status --short` clean.

## Checkpoint Results

- Implemented the `lowir2native` driver path, batch protocol handling, LowIR
  parsing, MIR dumping, and executable emission bridge.
- Added PA28 MIR lowering for direct scalar compare-fed branches, integer leaf
  chains, pointer/index arithmetic, switch dispatch, and basic `f32`/`f64`
  register/branch/value forms.
- Shared parser fixes now accept byte spans such as `copyobj 4`, negative CY86
  immediates, and LowIR floating exponent signs.
- Added native/MIR support for `bswap`, explicit integer/floating conversion
  MIR spellings, narrow integer normalization, and the PA28 atomic operation
  family: load/store, exchange, add-fetch, seq-cst store via `xchg`, and
  compare-exchange expected-value writeback.
- MIR frame metadata is now derived from the same register-allocation state
  used for the emitted body, so callee-saved preserves track actual temp
  ownership instead of a separate coarse heuristic.
- Added block-boundary register reuse, ABI-scratch object copy/zero MIR,
  destructive last-use index lowering, compare/branch materialization through
  `rax`, and direct return-value load handling.
- Added canonical indirect-call materialization through `r10` and made
  signal fences compile-time-only in the MIR dump.
- Added PA28-owned f80 validation/lowering/native emission, including f80
  parameter homes, memory-based f80 arithmetic, f80 direct calls/returns, f80
  structured global data, and x87 truncating integer conversion control-word
  handling.
- Added trivial parameter-slot promotion and call pass-mode address
  materialization so slot-backed object/reference arguments are represented
  from typed LowIR metadata rather than recovered from MIR text.
- Added PA28-owned native bridge support for indirect narrow-load aliases,
  direct scalar-pointer global call targets, thread-local MIR load/store address
  materialization, large integer ALU immediates, compact scalar stack homes, and
  caller result materialization.
- Audit cleanup removed the native-side CY86 text repair passes by moving
  native float literal bit emission, global alignment, and narrow indirect-load
  safety into typed emission in `lowir2cy86_emit.cpp` and
  `lowir2cy86_emit_helpers.cpp`; removed the non-contract
  `--dump-native-plan` alias; and changed unsupported MIR lowering from a
  placeholder comment to a hard error with explicit no-op simulation for valid
  jump/fence forms.

Final validation:

- `make test-report ACTIVE_TEST_REPORT_PAS='pa28'`: 106 / 106 PA28 tests pass.
- `make test-report-through-pa28`: 2527 / 2527 tests pass through PA28.
- `perl scripts/cppgm_file_audit.pl --stage pa28 --paths dev/src`: passes
  with warnings only.

Final PA28 coverage includes direct small-object copy/zero/return, f80 direct
calls, stack arguments beyond six, mixed GPR/XMM direct and indirect calls,
object parameter/result slot aliasing, direct temporary store-back cleanup,
runtime zero-only global alignment, switch call-case liveness, forwarded
parameter identity, single-use index call arguments, full-register indirect
calls, late indirect-call argument preservation, thread-local store pressure,
direct-call index-base preservation across SRET-like constructor paths, and
call pass-mode address materialization from typed LowIR metadata.

The PA28 backend is split into responsibility-named MIR dumper modules plus
shared MIR helper/op-name modules so file-size and function-size audit limits
are satisfied without include-as-implementation splitting.
