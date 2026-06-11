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

## Architecture Review

The implemented PA31 path follows the intended ownership split.  Source parsing,
semantic analysis, RTTI/typeinfo emission, and `throw` lowering remain in the
existing PA12/PA14 frontend.  `dev/src/pa14_lowir_throw.cpp` lowers C++ throws
and rethrows to LowIR calls annotated with host ABI runtime roles and `object=`
symbol metadata for `__cxa_allocate_exception`, `__cxa_throw`,
`_Unwind_Resume`, and `__gxx_personality_v0`.

`dev/src/pa29_toolchain.cpp` owns only the driver routing.  Compile-only output
whose destination is a `.o` still goes through the normal frontend-to-LowIR
pipeline, parses the temporary LowIR object, and hands the resulting typed
`lowir2cy86::Program` to PA31.  The earlier LowIR object path remains available
for non-`.o` compile output and staged link tests.

`dev/src/pa31_host_object.cpp` owns the host object format.  It builds ELF64
relocatable sections, symbols, RELA records, `.eh_frame`, `.gcc_except_table`,
CIE/FDE personality and LSDA references, type-table references, and host runtime
imports from the parsed LowIR program.  The implementation does not shell out to
host compilers, reference binaries, interpreters, VMs, trampolines, or copied
runtime payloads to produce the object file.

The audit found two cleanup items in that architecture: function symbols were
first registered with size zero before final code size was known, and the object
writer took the full LowIR program by value.  The cleanup removes the early
zero-size function symbol registration and passes the caller-owned parsed
program by mutable reference, matching the existing validation/layout mutation
and avoiding a full-program copy.

## Final Architecture Review

After audit cleanup, PA31 object emission remains a direct compiler backend path:
frontend facts are represented as LowIR roles and object metadata, the driver
selects the host object writer only for compile-only `.o` output, and the object
writer emits real ELF/EH sections and relocations from LowIR machine layout.
Private course EH globals are not emitted into PA31 host objects, and host EH
runtime helpers remain undefined imports for the host linker and unwinder.

The reviewed code has no PA31-specific fixture gates, skipped compiler phases,
dummy object output, embedded earlier-IR payloads, timeout workarounds, or
file-audit bypasses.  Remaining file-audit warnings are pre-existing shared
module organization warnings outside the new PA31 object writer and do not hide
PA31 implementation fragments.
