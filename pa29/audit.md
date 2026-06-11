# PA29 Audit

## Audit Plan

Audit scope:

- Driver and PA29 boundary: `dev/cppgm++.cpp`, `dev/src/pa29_toolchain.cpp`,
  `dev/src/pa29_toolchain.h`, and `dev/frontend_source_sets.mk`.
- Object and native backend boundary: `dev/src/cy86_elf_object.cpp`,
  `dev/src/cy86_elf_object.h`, `dev/src/cy86_model.cpp`,
  `dev/src/cy86_model.h`, `dev/src/cy86_support.cpp`,
  `dev/src/cy86_x86.cpp`, `dev/src/cy86_x86.h`,
  `dev/src/lowir2cy86*.cpp`, `dev/src/lowir2native*.cpp`, and the PA29
  runtime emitter.
- Source pipeline boundaries touched for PA29: `dev/src/preproc_support.*`,
  `dev/src/posttoken_support.*`, `dev/src/nsinit_model.cpp`,
  `dev/src/pa11_model.cpp`, `dev/src/pa12_*.cpp`, and
  `dev/src/pa14_lowir*.cpp`.
- Runtime shim: `dev/include/exception`.

Ownership boundaries to inspect:

- `cppgm++` must only route options and modes; it must not special-case PA29
  fixtures or bypass compile phases.
- Source inputs must flow through preprocessing, parsing, semantics, and PA14
  LowIR lowering independently per translation unit.
- Compiler-owned object files may carry LowIR/link facts, but link mode must
  merge those facts explicitly rather than recovering semantic facts by ad hoc
  source or test-shape scans.
- ELF helper objects belong to the PA29 link/backend boundary; imported
  sections, symbols, and relocations must feed the existing native image
  builder, not a copied runtime or template executable.
- Include search belongs to preprocessor options and must not rewrite source.

Performance risks to inspect:

- Repeated whole-program scans while coalescing object symbols or rewriting
  per-translation-unit names.
- Quadratic section, relocation, or symbol lookups in ELF object import.
- Excessive string copying when parsing and concatenating compiler-owned
  objects.
- Hot-path recomputation in LowIR validation, native emission, exception
  lowering, and namespace-scope init/fini synthesis.

File-audit issues to inspect:

- New `dev/src/*.cpp` files must be listed in the appropriate source set.
- Implementation must remain in checked `dev/` and `dev/src/` paths, with no
  hidden fragments, generated payloads, fixture-specific gates, or weakened
  audit checks.
- PA handout files and references must remain test fixtures, not implementation
  storage.

## Findings

1. PA29 user include paths were appended after the compiler shim include paths.
   That meant `-I` could not override an internal shim header such as
   `dev/include/exception`, which contradicted the intended PA29 include-search
   boundary.

2. Duplicate global symbols from ELF helper objects were silently accepted. The
   native backend seeded helper-object labels in a `map`, so two libraries that
   defined the same C symbol could overwrite each other instead of failing as a
   duplicate global definition.

3. Compile mode accepted unsupported `--target` values because target
   validation only happened in link/native output mode. PA29's target handling
   needs to fail consistently for `-c` and link invocations.

4. The audit did not find reference-binary callouts, host compiler/linker
   delegation in the implementation path, fixture-name gates, embedded binary
   payloads, copied runtimes, timeout workarounds, or file-audit bypasses. The
   file-audit warnings inspected in touched semantic/lowering files are long
   compiler-source lines or established ownership warnings, not hidden payloads
   or unchecked implementation fragments.

## Changes Made

- Updated `dev/cppgm++.cpp` so PA29 driver invocations search user `-I` paths
  before internal shim include directories.
- Updated `dev/src/pa29_toolchain.cpp` so `cppgm++ -c --target ...` validates
  the target before writing an object.
- Updated `dev/src/cy86_x86.cpp` so external ELF helper symbols reserve their
  raw, global-label, and function-thunk labels before source layout; duplicate
  helper definitions now fail instead of overwriting an earlier label.
- Added PA29 course regressions under `cppgm.tests/course/pa29/` for user
  include precedence and duplicate helper-object symbols.

## Validation

Completed during audit:

```sh
make -C pa29 check TEST=course/pa29/200-user-include-overrides-internal.t
make -C pa29 check TEST=course/pa29/200-duplicate-helper-symbol-bad.t
make test-report ACTIVE_TEST_REPORT_PAS='pa29'
make test-report-through-pa29
perl scripts/cppgm_file_audit.pl --stage pa29 --paths dev/src
```

Results:

- targeted PA29 include-order regression: pass
- targeted PA29 duplicate-helper-symbol regression: pass
- PA29 report slice: pass, `70 / 70`
- required through-stage report: pass, `2597 / 2597`
- file audit: pass, with warnings only
