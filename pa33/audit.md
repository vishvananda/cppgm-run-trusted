# PA33 Audit

## Audit Plan

- Re-read the PA33 contract and compare the implementation against the
  required host ABI/runtime surfaces: vtable ownership, RTTI ownership,
  `dynamic_cast`, `typeid`, covariant thunks, deleting destructors, richer host
  EH behavior, and inspected object facts.
- Inspect the PA33 implementation commit across these files:
  `dev/cppgm++.cpp`, `dev/frontend_source_sets.mk`, `dev/include/exception`,
  `dev/include/stdexcept`, `dev/include/typeinfo`, `dev/src/lowir2cy86*`,
  `dev/src/pa11_*`, `dev/src/pa12_*`, `dev/src/pa14_lowir*`,
  `dev/src/pa29_toolchain*`, and `dev/src/pa31_host_object*`.
- Check ownership boundaries:
  semantic facts must be represented in `pa11`/`pa12`, ABI spelling and LowIR
  metadata in `pa14_lowir*`, and ELF/relocation/call-frame details in
  `pa31_host_object*`; the object writer should not reconstruct high-level C++
  facts from strings.
- Check performance risks in hot paths: template substitution and ABI mangling
  substitution lists, RTTI/vtable emission walks, dynamic-cast base-offset
  lookup, host object lowering, relocation emission, and through-suite driver
  behavior. Look for avoidable quadratic scans, repeated full-program walks,
  excessive value copies, and recomputation inside per-instruction or
  per-symbol loops.
- Check for forbidden shortcuts: skipped compiler phases, dummy outputs,
  interpreter/VM/trampoline/template-binary or embedded-payload substitutes,
  fixture-specific gates, source-shape checks, timeout workarounds, reference
  binary shell-outs, host compiler output used as required compiler output, or
  hidden implementation fragments outside audited source paths.
- Check file-audit risks: new `dev/src/*.cpp` membership in
  `dev/frontend_source_sets.mk`, file sizes near audit thresholds, source moved
  outside `dev/src`, generated `.my` artifacts, weakened scripts, or bypasses
  in unchecked paths.
- Review recent PA33 tests and inspect sidecars to ensure implementation
  behavior is semantic and ABI-driven rather than hardcoded to individual test
  names or exact fixture source shapes.

## Findings

- Blocker: `pa14_lowir_rtti.cpp` selected the vtable/RTTI owner by scanning for
  any out-of-line virtual function definition in the TU. That allowed a TU that
  defines a later virtual member to emit key-function-owned vtables/RTTI. The
  first fix exposed a related parser-model detail: out-of-class definitions can
  be represented as duplicate member bindings, so the owner check must match the
  selected key declaration to same-owner, same-name, same-type definition
  bindings.
- Blocker: `__builtin_alloca` was modeled as a declared function with
  `object=malloc`. That made the tested host object link while substituting heap
  allocation for stack allocation.
- File-audit blocker: adding stack allocation directly to
  `FuncGen::emit_value_instruction` made that dispatcher exceed the PA33
  function-size limit.
- No additional audit blockers were found in the scanned PA33 implementation:
  no reference-binary shell-outs, host compiler output substitution, fixture
  gates, skipped compiler phases, embedded payloads, hidden source paths, or
  weakened file-audit checks were found in the touched implementation.

## Changes Made

- Updated RTTI/vtable key-function ownership to walk class declaration order,
  choose only the first eligible key function, and treat duplicate out-of-class
  definition bindings as definitions of that key only when owner, name, and type
  match.
- Replaced the fake `__builtin_alloca` declaration with a typed `stackalloc`
  LowIR instruction, parser/validator support, explicit CY86 rejection, and
  host-object lowering that subtracts a 16-byte-aligned byte count from `rsp`.
- Split host stack allocation lowering into `FuncGen::emit_stack_alloc` so the
  host object dispatcher stays under file-audit size limits.
- Added PA33 course regressions for key-function ownership and alloca stack
  allocation behavior under `cppgm.tests/course/pa33/`.

## Validation

- `make -C pa33 check TEST=tests/general/200-host-builtin-alloca-link-smoke.t`
  passed.
- `make -C pa33 check TEST=course/pa33/200-host-builtin-alloca-stackalloc.t`
  passed.
- `make -C pa33 check TEST=tests/general/200-host-eh-cross-tu-rtti-base-coalescing.t`
  passed after the duplicate-binding key-definition fix.
- `make -C pa33 check TEST=course/pa33/200-host-key-function-order-import.t`
  passed.
- `make test-report-through-pa33` passed on the final source:
  `2833 / 2833` tests.
- `perl scripts/cppgm_file_audit.pl --stage pa33 --paths dev/src` passed with
  the existing 28 warnings and no fatal issues.
