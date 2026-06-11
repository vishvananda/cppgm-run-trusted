# PA31 Implementation Plan

## Goal

Make `cppgm++ -c` emit a host-linkable x86_64 Linux relocatable object for
the existing frontend/LowIR pipeline, including the host exception-handling
facts required by the PA31 tests.

## Design

- Keep source parsing, semantic analysis, and LowIR lowering owned by the
  existing PA10-PA14 code. PA31 consumes typed LowIR plus metadata roles such
  as `eh_throw`, `eh_begin_catch`, `eh_resume`, and object symbol names.
- Extend the compile-only driver path in `pa29_toolchain` so PA31 object mode
  no longer writes LowIR text to the requested `.o`; it should lower the unit
  to native host object data.
- Add a cohesive native object-emission layer under `dev/src` rather than
  placing ELF/EH layout code in the driver. The object layer owns:
  - ELF64 relocatable sections, symbols, and RELA records.
  - Host ABI symbol names from LowIR `object=` metadata.
  - `.text`, `.rodata`/data, `.eh_frame`, and `.gcc_except_table`.
  - Host EH call-site/action/type-table facts derived from LowIR EH
    instructions, not source text.
- Keep private course exception runtime symbols out of host objects. Calls to
  `__cxa_*`, `_Unwind_Resume`, and `__gxx_personality_v0` remain undefined
  host imports.
- Preserve earlier PA behavior by limiting the new object path to compile-only
  host object output. Existing LowIR merge/link behavior remains available for
  earlier staged link tests.

## Validation

- Use `make test-report ACTIVE_TEST_REPORT_PAS='pa31'` for scoped diagnosis.
- After object emission or shared lowering changes, run
  `make test-report-through-pa31`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa31 --paths dev/src`.
- Commit cohesive progress only after a stable build/test checkpoint.
