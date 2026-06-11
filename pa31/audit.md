# PA31 Audit

## Audit Plan

- Re-read the PA31 contract in `pa31/README.md`, the implementation plan in
  `pa31/plan.md`, and the test/reference rules in
  `TESTING_AND_REFERENCES.md`.
- Inspect the PA31 implementation commit and its changed implementation files:
  `dev/src/pa31_host_object.cpp`, `dev/src/pa31_host_object.h`,
  `dev/src/pa29_toolchain.cpp`, `dev/src/pa14_lowir_throw.cpp`,
  `dev/src/pa14_lowir_function_order.cpp`, `dev/src/pa12_records.cpp`, and
  `dev/frontend_source_sets.mk`.
- Inspect `pa31/tests/general/` and the latest full-stage log at
  `/home/vishvananda/work/.ralph/trusted-gpt-5.5-xhigh/last-test.log` for the
  covered behavior and any hidden failures or skipped paths.
- Check ownership boundaries:
  frontend/source semantics must lower to LowIR EH roles and object metadata;
  `pa29_toolchain` may route compile-only `.o` output but must not fake host
  results; `pa31_host_object` must own ELF, relocations, `.eh_frame`, LSDA, and
  host ABI symbol emission from LowIR facts rather than source text.
- Check for substitutes or bypasses: no interpreter/VM/trampoline/template
  binary, embedded earlier-IR payload, host compiler shell-out, reference
  binary shell-out, dummy object bytes, private `cppgm_eh_*` symbols in PA31
  host objects, source-shape gates, fixture-specific gates, or fallback success
  paths.
- Check performance risks: repeated full-suite/test walks, avoidable quadratic
  scans in object symbol emission and function ordering, hot-path full metadata
  searches, unbounded byte-at-a-time copy/zero expansion, and repeated layout or
  parse work that could block PA31-scale inputs.
- Check file-audit issues: new `dev/src` files are listed in
  `dev/frontend_source_sets.mk`; implementation remains in audited paths; no
  hidden fragments, weakened checks, generated `.my`/reference edits, oversized
  unchecked files, or code moved outside `dev/src`.
- Validate with `make test-report-through-pa31` and
  `perl scripts/cppgm_file_audit.pl --stage pa31 --paths dev/src` after fixes.

## Findings

- The PA31 implementation is in the expected audited ownership boundary:
  `dev/src/pa29_toolchain.cpp` routes compile-only `.o` output, while
  `dev/src/pa31_host_object.cpp` emits ELF64 sections, symbols, relocations,
  `.eh_frame`, and `.gcc_except_table` directly from parsed LowIR facts.
- `dev/src/pa14_lowir_throw.cpp` lowers throws to host EH runtime-role calls and
  host `object=` symbol metadata.  The object writer consumes those roles and
  metadata; it does not inspect source text or test names.
- No interpreter, VM, trampoline, template-binary, copied-runtime,
  embedded-payload, host-compiler shell-out, or reference-binary shell-out path
  was found in the PA31 implementation.
- No fixture-specific gates, timeout/sleep workarounds, `.ref`/`.my` reads, or
  private `cppgm_eh_*` host-object symbols were found in the changed source.
- Function symbols were registered before code emission with size `0`, then the
  later registration with the real size was ignored by the duplicate-symbol
  guard.  Linkers tolerated this, but it produced weaker ELF symbol metadata.
- `pa31::write_host_object` took the full `lowir2cy86::Program` by value even
  though the caller owns the mutable parsed program and the writer immediately
  validates/layouts it.  This was avoidable compile-only object output copying.
- `dev/src/pa31_host_object.cpp` is registered in
  `dev/frontend_source_sets.mk`.  The required file audit passes; its warnings
  are pre-existing shared-module organization warnings outside the PA31 object
  writer and do not indicate hidden PA31 code or file-audit bypasses.

## Changes Made

- Changed `pa31::write_host_object` to accept `lowir2cy86::Program&`, removing
  the avoidable full-program copy on the `.o` compile path.
- Removed the early zero-size function symbol registration from
  `FuncGen::emit`; function symbols are now emitted once after final code size
  is known.
- Added this audit document and updated `pa31/plan.md` with Architecture Review
  and Final Architecture Review sections grounded in the implemented PA31
  backend.

## Validation

- `make test-pa31` passed after the cleanup.
- A manual temp-object inspection of
  `pa31/tests/general/100-host-eh-same-tu-throw-catch.t.1` showed nonzero ELF
  function symbol sizes for `_Z1fv` and `main`, and no global
  `cppgm_eh`/`__cppgm_eh` symbols.
- `make test-report-through-pa31` passed: 2680/2680 tests through PA31.
- `perl scripts/cppgm_file_audit.pl --stage pa31 --paths dev/src` passed with
  26 warnings, all on pre-existing shared modules outside the PA31 object
  writer.
