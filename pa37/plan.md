# PA37 LowIR Optimizer Plan

## Ownership

- Keep the LowIR parser, validator, and typed IR ownership in the existing
  `lowir2cy86::Program` model.
- Add a reusable `lowiropt` support layer under `dev/src/` for parse, optimize,
  canonical LowIR dump, and file writing.
- Keep `dev/lowiropt.cpp` as command-line plumbing only.
- Route `cppgm++ --emit-lowir -O*`, compile, and link paths through the same
  optimizer before object/native lowering.

## Design

- `-O0`: parse LowIR, validate/layout, then dump canonical LowIR without
  transforms.
- `-O1`: run a deterministic fixed-point over functions:
  constant/copy propagation, local pure expression reuse, algebraic folding,
  branch/switch folding, CFG reachability and jump cleanup, pure DCE, safe
  readnone call DCE, dead direct-slot traffic removal, and small direct-call
  inlining.
- `-O2`: run `-O1`, then conservative direct scalar slot promotion and another
  `-O1` cleanup pass.
- Rebuild function temp/type maps by revalidating after transforms instead of
  recovering semantic facts from emitted text.
- Preserve EH structure conservatively: do not remove handler blocks, EH marker
  blocks, or protected-region edges unless the function is known non-unwinding
  and the region has no possible transfer to the handler.

## Validation

- Fast diagnosis: `make test-report ACTIVE_TEST_REPORT_PAS='pa37'`.
- After meaningful implementation checkpoints: `make test-report-through-pa37`.
- Required final checks:
  - `make test-report-through-pa37`
  - `perl scripts/cppgm_file_audit.pl --stage pa37 --paths dev/src`

## Architecture Review

- The PA37 optimizer is owned by `dev/src/lowiropt_*` with
  `dev/lowiropt.cpp` limited to CLI parsing and file-level plumbing.
  `cppgm++ --emit-lowir`, compile, and link paths route through the same
  `lowiropt::optimize_program` entry point instead of maintaining a parallel
  optimization path.
- The optimizer operates on `lowir2cy86::Program`, `Function`, `Block`, and
  `Instruction` data. Semantic facts are rebuilt with `rebuild_program` and
  LowIR validation rather than recovered from dumped text.
- Validation has two explicit ownership modes: executable validation still
  requires entry resolution, while optimizer and host-object fragment
  validation/layout can validate LowIR fragments without synthesizing an entry.
- O1 is a deterministic model transform over constants, copies, pure
  expressions, CFG cleanup, DCE, direct-slot cleanup, EH-preserving cleanup, and
  small direct-call inlining. O2 layers conservative scalar slot promotion on
  top of O1 and then runs O1 cleanup again.
- Inlining remains bounded by semantic eligibility: declarations, recursive
  callees, EH callees, active protected regions, and large non-preferred
  callees are rejected. The inliner batches only within the first active
  priority tier, preserving the existing high-priority entry/callee ordering
  while avoiding repeated whole-program walks in large same-tier library code.
- Host object emission now validates and lays out LowIR object fragments through
  the LowIR validator directly; it does not depend on stale cached maps or fake
  executable entry markers.

## Final Architecture Review

- No skipped compiler phase, fallback success path, reference-binary shell-out,
  host-compiler output substitute, interpreter, VM, trampoline, templated
  binary, copied runtime, or embedded earlier-IR payload path remains in PA37.
- Invalid LowIR is rejected by the optimizer before and after transforms. O0
  still parses and dumps; O1/O2 validate the same typed model they transform.
- The previous pass-count caps were removed. Termination is based on real IR
  change detection, and large-program inlining is handled by deterministic
  priority-tier batching plus whole-caller result replacement for multi-block
  inlines.
- EH regions remain conservative: handler edges are preserved in CFG analysis,
  active-EH inlining is restricted, and slot/result propagation now accounts
  for dominated cleanup-block uses.
- Source ownership remains under `dev/` and `dev/src`; the new validator object
  is listed for `lowiropt` in `dev/frontend_source_sets.mk`, and file audit
  reports no new bypass or unchecked implementation path.
- Final checks passed with `make test-report-through-pa37` and
  `perl scripts/cppgm_file_audit.pl --stage pa37 --paths dev/src`.
