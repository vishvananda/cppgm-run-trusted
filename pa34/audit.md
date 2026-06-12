# PA34 Audit

## Audit Plan

Audit the PA34 full-stage implementation against `pa34/README.md`,
`pa34/plan.md`, the recent implementation commit, and the PA34 preproc/compile
and through-PA34 test surfaces.

Files and ownership boundaries to inspect:

- Driver and toolchain control: `dev/cppgm++.cpp`,
  `dev/src/pa29_toolchain.cpp`, `dev/src/pa29_toolchain.h`.
- Hosted preprocessor state and include/macro behavior:
  `dev/src/preproc_support.cpp`, `dev/src/preproc_support.h`,
  `dev/src/posttoken_pipeline.cpp`, `dev/src/posttoken_support.cpp`,
  `dev/src/pptoken_lib.cpp`, `dev/src/macro_support.cpp`.
- Parser, semantic, and template ownership:
  `dev/src/pa11_internal.h`, `dev/src/pa11_model.cpp`,
  `dev/src/pa12_internal.h`, `dev/src/pa12_semantics.h`,
  `dev/src/pa12_decls*.cpp`, `dev/src/pa12_expr*.cpp`,
  `dev/src/pa12_templates*.cpp`, `dev/src/pa12_types*.cpp`,
  `dev/src/pa12_constexpr*.cpp`, and `dev/src/nsinit_eval.cpp`.
- Lowering, object emission, and hosted builtin runtime surfaces:
  `dev/src/pa14_lowir*.cpp`, `dev/src/pa14_lowir*.h`,
  `dev/src/pa31_host_object.cpp`, and
  `dev/src/pa31_host_object_internal.h`.
- Build/file-audit integration: `dev/Makefile`,
  `dev/frontend_source_sets.mk`, and the set of new `dev/src/*.cpp` files.

Specific risks to check:

- Earlier-stage regressions from shared preprocessor, parser, semantic,
  template, LowIR, or host-object changes.
- Skipped compiler phases, fallback success paths, dummy or minimal output
  generation, embedded payloads, template binaries, trampolines, copied
  runtime substitutes, or shell-outs to reference/host tools for compiler
  output.
- Test-specific/source-shape acceptance gates, timeout workarounds, file-audit
  bypasses, hidden implementation fragments, or code moved to unchecked paths.
- Stringly semantic facts, duplicated ownership, and downstream recovery of
  facts that should be represented earlier in parser/semantic/type/template
  nodes.
- Performance blockers such as repeated full-suite or full-AST walks, avoidable
  quadratic scans in template matching/substitution, excessive copying in hot
  paths, repeated include probing, and recomputation during class-template
  instantiation or LowIR emission.
- File-audit risks from newly added source files not listed in
  `dev/frontend_source_sets.mk`, oversized hidden files, or weakened audit
  checks.

## Findings

- Found and fixed a hosted builtin ownership mismatch. `__has_builtin`
  advertised `__is_invocable_r`, `__is_signed`, and `__builtin_memset`, but the
  parser/semantic/builtin lowering surface did not fully implement those
  advertised facts. That could send hosted headers down compiler-builtin
  branches that later failed semantically or during object emission.
- Reviewed the PA34 driver/preprocessor path and did not find reference-binary
  shell-outs, host-compiler output substitution, dummy preprocessor/object
  output, fallback success returns, or PA34 test-path checks.
- Reviewed hosted semantic gates around vendor trait templates. The remaining
  hosted compatibility checks are constrained to semantic template records and
  member `value` lookup; they do not inspect source filenames or test fixture
  names, and they still run through parser/template/constexpr state.
- Reviewed new `dev/src/*.cpp` ownership. The new implementation files are in
  the `cppgm++` source set, and the file audit reports no fatal issues or
  unchecked source movement. The remaining audit warnings are responsibility
  size/duplication warnings in audited files, not bypasses.
- Reviewed the performance-sensitive PA34 paths touched by this cleanup.
  Include lookup walks configured include paths, builtin trait evaluation uses
  stored type/template arguments and normal unevaluated call conversion, and
  LowIR builtin declarations are direct declarations. No timeout workaround,
  repeated full-suite walk, or avoidable hot-path recomputation blocker was
  found.

## Changes Made

- Added parser and semantic support for `__is_invocable_r(...)` using the
  existing unevaluated `make_call_expr` path plus conversion to the requested
  result type.
- Added semantic support for `__is_signed(...)` from the typed fundamental and
  enum-underlying type model.
- Added real hosted `__builtin_memset` support through builtin function
  recognition, typed binding creation, and PA14 LowIR declaration mapped to the
  host `memset` symbol.
- Aligned the PA34 `__has_builtin` probe table with the audited hosted builtin
  and type-trait surface.
- Added focused course PA34 compile regressions under
  `cppgm.tests/course/pa34/compile/` for builtin probe/trait alignment and
  `__builtin_memset`.
- Updated `pa34/plan.md` with Architecture Review and Final Architecture
  Review grounded in the current implementation.

## Validation

- `make -C pa34 test` passed after the cleanup, including the new course PA34
  compile tests.
- `make test-report-through-pa34` passed: 3106/3106 tests, PA1 through PA34.
- `perl scripts/cppgm_file_audit.pl --stage pa34 --paths dev/src` passed with
  29 warnings and no fatal file-audit issue or bypass.
- `git diff --check` passed.
