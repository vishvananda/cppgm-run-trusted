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

