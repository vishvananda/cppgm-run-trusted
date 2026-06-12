# PA34 Implementation Plan

## Scope

PA34 continues the existing `cppgm++` driver and compiler pipeline. The work is
split across the hosted preprocessor surface, parser concessions used by hosted
headers, builtin traits/transforms, and builtin intrinsic lowering needed for
compile-only hosted sources.

## Design

- Keep implementation changes in `dev/` and `dev/src/`.
- Wire `cppgm++ -E` to `preproc::run_preproc` so it emits the same structured
  posttoken stream as the PA5 `preproc` frontend.
- Extend `preproc::Options` to carry real driver state:
  - user `-D` definitions and `-U` removals
  - `-include` files to process before the primary source
  - user include paths and system include paths in command-line order
  - hosted standard include paths imported from the generated host config
- Keep hosted macro behavior in the shared preprocessor/macro support rather
  than in PA34 scripts. Compile mode must use the same options as `-E`.
- Add hosted control-expression probes as function-like macros or typed
  preprocessor callbacks:
  - `__has_builtin`
  - `__has_feature` / `__has_extension`
  - `__has_attribute` / `__has_cpp_attribute`
  - `__building_module`
  - `__has_include` / `__has_include_next`
- Implement `#include_next` in the normal include resolver with enough include
  stack state to resume after the directory that supplied the current header.
- Preserve PA5 behavior for conditional groups, `#pragma once`, `_Pragma`,
  ordinary includes, and structured token output.
- Keep GNU/Clang parser concessions local to the shared PA12 parser:
  attributes in declaration and namespace positions, GNU decl-spec aliases,
  nullable pointer qualifiers, block pointers, GNU asm labels/statements,
  hosted builtin type spellings, and type-trait expressions.
- Represent builtin type traits as typed boolean expressions during parsing and
  semantic evaluation. Dependent trait operands should remain dependent instead
  of being recovered from formatted type text.
- Implement builtin type transforms in the existing type helper layer so alias
  templates and template substitutions reuse normal type ownership.
- Add hosted intrinsics as ordinary builtin entities in expression semantics and
  lower constant or codegen-required forms through the existing backend. Do not
  substitute runtime drivers or fixture-specific answers.
- Keep hosted literal/type compatibility in the lexer and typed expression
  layers: binary literals, GNU hex-float forms, vendor float suffixes, `_FloatN`
  spellings, `_BitInt`, `__int128`, and GNU pointer qualifiers should lower to
  existing fundamental and pointer types.
- Let dependent template constructs stay dependent when the hosted headers use
  library implementation patterns that cannot be completed at declaration parse
  time. This includes dependent dereference/subscript, dependent conversion
  checks, dependent `__integer_pack`, and validation-time member bodies.
- Register and look up hosted class templates through the normal namespace and
  class-template tables, including forward declarations, specializations, and
  qualified template-ids from vendor namespaces such as `::std`.

## Validation

Use focused checks during implementation:

```sh
make -C pa34 check TEST=tests/preproc/300-elif-after-taken-branch.t
make -C pa34 check TEST=tests/preproc/300-has-include.t
make -C pa34 check TEST=tests/preproc/300-include-next.t
make -C pa34 check TEST=tests/compile/500-builtin-transforms-and-traits.t
make -C pa34 check TEST=tests/compile/500-builtin-bswap-family.t
make test-report ACTIVE_TEST_REPORT_PAS='pa34'
```

After shared preprocessor or driver changes, run the required full gate:

```sh
make test-report-through-pa34
perl scripts/cppgm_file_audit.pl --stage pa34 --paths dev/src
```

Older-stage regressions found by the through report are blockers and must be
fixed before treating PA34 progress as complete.

## Current Work Queue

- Done: shared preprocessor conditionals and hosted include probes are wired far
  enough for the PA34 preprocessor set.
- Done: GNU designated initializers and `(T){...}` compound literals parse into
  typed braced initializer nodes and lower through aggregate initialization.
- Done: implemented the remaining object-model compile gaps for
  `[[no_unique_address]]` field layout, GNU zero-length member arrays,
  recursive `operator->`, and class structured bindings.
- Done: hosted template semantic gaps for templated lambda instantiation/default
  arguments, lazy using imports, nested pack aliases, function-reference
  constructibility, and hosted invocability traits are implemented in the shared
  PA12 semantic and template-substitution paths.
- Done: hosted class-template registration remains lazy for definition
  validation. Non-hosted PA12/PA14 semantic modes still eagerly replay template
  definitions for course diagnostics, while PA34 driver mode records hosted
  templates and instantiates demanded specializations through the normal class
  template path.
- Done: hosted builtin runtime lowering for memory/string/new-delete/math and
  overflow smoke tests is implemented through typed call nodes, LowIR emission,
  and the existing PA31 object writer/native backend paths.
- Done: focused regressions, scoped PA34 report, required
  `make test-report-through-pa34`, and `scripts/cppgm_file_audit.pl --stage
  pa34 --paths dev/src` pass.
