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

## Validation

- First run `make test-report ACTIVE_TEST_REPORT_PAS='pa38'` while iterating on
  PA38 MIR shape.
- After meaningful backend changes, run `make test-report-through-pa38`.
- Run `make -C pa38 test-debuginfo` to check debug metadata preservation.
- Run `perl scripts/cppgm_file_audit.pl --stage pa38 --paths dev/src`.
- Commit cohesive changes and verify `git status --short` is clean.
