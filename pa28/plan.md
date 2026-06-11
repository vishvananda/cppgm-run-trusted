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
- Current validation:
  - `make test-report ACTIVE_TEST_REPORT_PAS='pa28'`: 36 / 106 PA28 tests pass.
  - `make test-report-through-pa28`: PA1-PA27 pass; PA28 remains failing,
    2458 / 2527 total.
  - `perl scripts/cppgm_file_audit.pl --stage pa28 --paths dev/src`: pass
    with the existing 24 warnings.

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

Remaining work is concentrated in strict raw-MIR parity, f80 native execution,
richer call ABI/liveness, object-slot alias cases, and larger register-pressure
structural cases.
