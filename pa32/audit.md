# PA32 audit

## Audit Plan

Inspect the PA32 implementation against `pa32/README.md`,
`TESTING_AND_REFERENCES.md`, `pa32/plan.md`, and the current `HEAD` changes in
`dev/` before accepting the stage as complete.

Files and ownership boundaries to inspect:

- `dev/src/pa12_decls*.cpp`, `dev/src/pa12_decl_variables.cpp`,
  `dev/src/pa12_types_declspec.cpp`, `dev/src/pa12_names.cpp`, and
  `dev/src/pa12_internal.h` for declaration ownership, C linkage collision
  checks, attributes, static/thread-local storage facts, and preservation of
  typed semantic facts instead of downstream string recovery.
- `dev/src/pa12_templates*.cpp`,
  `dev/src/pa12_templates_function_abi*.cpp`,
  `dev/src/pa12_templates_function_support.h`, and
  `dev/src/pa12_templates_member_*.cpp` for ABI mangling, template argument and
  substitution ownership, replay of dependent member bodies, and avoidance of
  test-shape or source-text gates.
- `dev/src/pa14_lowir*.cpp`, `dev/src/pa14_lowir_internal.h`, and
  `dev/src/lowir2cy86_*.cpp` for LowIR metadata propagation, function ordering,
  global/TLS metadata, constructor/lifecycle emission, RTTI/vtable facts, and
  absence of dummy or minimal output paths.
- `dev/src/pa31_host_object.cpp`,
  `dev/src/pa31_host_object_internal.h`,
  `dev/src/pa31_host_object_elf.cpp`,
  `dev/src/pa31_host_object_globals.cpp`, and
  `dev/src/pa31_host_object_eh.cpp` for ELF sections, relocations, weak/comdat
  behavior, TLS wrappers, EH/LSDA data, symbol selection, and rejection of
  interpreter/VM/trampoline/template-binary or embedded-payload substitutes.
- `dev/frontend_source_sets.mk`, `dev/include/exception`, and
  `dev/include/stdexcept` for source-set/file-audit coverage and hidden-runtime
  or copied-runtime risks.
- PA32 tests under `pa32/tests/general/` and course tests under
  `cppgm.tests/course/pa32/` for coverage of host object interoperability,
  symbol inspection, TLS, duplicate definitions, and negative compile/link
  cases.

Performance risks to inspect:

- repeated full-program or full-template scans during function ordering,
  template member replay, and object-symbol construction;
- avoidable quadratic substitution-name construction or vector copying in the
  ABI mangler hot path;
- repeated section/symbol-table lookups during ELF emission that should be
  indexed once;
- recompilation or re-instantiation loops hidden behind successful tests.

File-audit issues to inspect:

- new `dev/src/*.cpp` entries are listed in `dev/frontend_source_sets.mk`;
- implementation was not moved to unchecked paths or hidden in generated
  sidecars;
- file-size warnings are handled by real splits rather than bypassing the
  checker;
- required validation includes
  `perl scripts/cppgm_file_audit.pl --stage pa32 --paths dev/src`.

## Findings

1. `cppgm++ -c -o <objfile>` selected the PA31 host object writer only when
   `<objfile>` ended in `.o`. The PA32 contract requires an ordinary
   relocatable object for the requested output file name, so extensionless or
   non-`.o` host-object names could still receive the older PA29 LowIR object
   format. This was a contract blocker, not a test failure in the current
   fixture set.
2. The PA31 host object prologue assumed every integer-like parameter arrived in
   one of the six System V integer registers. A PA32 template-mangling test with
   seven parameters exposed the out-of-bounds register read when the first audit
   hardening check was added. The writer also needed coherent handling for
   stack-passed direct-object parameters so a two-slot object is copied wholly
   from registers or wholly from the caller stack.
3. The required through-stage report exposed an earlier-stage performance
   blocker: `pa3/tests/300-triple.t` was close enough to the PA3 text-test
   timeout that report-mode parallel load produced repeated timeouts. The
   underlying `ctrlexpr` path was doing repeated literal/identifier conversion
   and many small result writes for a half-million-line input. This was fixed as
   a general hot-path improvement, not by changing timeout settings.
4. The inspected PA12, PA14, PA29, and PA31 paths do not shell out to reference
   binaries, the host compiler, interpreters, VMs, object templates, or copied
   runtime payloads to satisfy PA32. Semantic facts flow from PA12 bindings and
   template declarations into PA14 LowIR metadata, then into PA31 ELF emission.
5. Existing file-audit warnings identify dense or split ownership areas, but no
   unchecked implementation fragment, hidden source-set bypass, file-audit
   bypass, fixture gate, or dummy output generator was found.

## Changes Made

- Updated `dev/src/pa29_toolchain.cpp` so compile mode writes host ELF
  relocatable objects for every non-`.obj` output name. The `.obj` suffix remains
  the PA29 LowIR-object compatibility surface used by earlier through-stage
  tests.
- Updated `dev/src/pa31_host_object.cpp` and
  `dev/src/pa31_host_object_internal.h` so the host object prologue copies
  incoming stack-passed scalar, float, and direct-object parameters from the
  caller frame. Direct two-slot objects now follow an all-register or all-stack
  choice instead of mixing the last available register with a stack slot.
- Updated `dev/src/ctrlexpr_support.cpp` to cache repeated control-expression
  literal and identifier token conversions and buffer result output until EOF.
  The PA5 `defined` compatibility case for identifier-like operator tokens is
  preserved by retaining source text for those operator names.
- Updated `pa32/plan.md` with `Architecture Review` and
  `Final Architecture Review` sections grounded in the actual PA32 pipeline and
  audit cleanup.

## Validation

- `make test-pa32` passes: `pa32 tests: PASS (77/77)`,
  `pa32 course/pa32: PASS (0/0)`.
- `make test-pa3` passes: `pa3 tests: PASS (8/8)`,
  `pa3 ../cppgm.tests/course/pa3: PASS (11/11)`.
- `make test-pa5` passes: `pa5 tests: PASS (62/62)`,
  `pa5 course/pa5: PASS (6/6)`.
- `./dev/ctrlexpr < pa3/tests/300-triple.t` matches
  `pa3/tests/300-triple.ref`; the measured wall time improved from about
  9.97 seconds before the cleanup to about 4.64 seconds after it.
- Manual contract check for `cppgm++ -c -o` with an extensionless output name
  produced an ELF64 x86-64 relocatable object.
- `make test-report-through-pa32` passes:
  `ALL TESTS PASSED SUCCESSFULLY! (2757 / 2757)`.
- `perl scripts/cppgm_file_audit.pl --stage pa32 --paths dev/src` passes with
  28 warnings and no errors.
