# PA8 Implementation Plan

## Scope

Implement `nsinit` as the next frontend stage on top of the existing
preprocessor and posttoken pipeline.  The PA8 code will live in `dev/src` as a
separate support layer so PA7 `nsdecl` output remains unchanged.

## Design

- Add an `nsinit` support API used by `dev/nsinit.cpp`.
- Parse PA8 translation units into typed compiler state:
  - namespaces, namespace aliases, using declarations/directives, type aliases,
    variables, functions, storage/function specifiers, definitions, and
    initializers;
  - expression nodes for literals, id-expressions, and parenthesized
    expressions, with lexical order for string literals.
- Perform semantic checks during parse/collection where scope rules are local:
  namespace alias misuse, namespace conflicts, qualified declarations outside
  enclosing namespaces, invalid reference/object types, function overloading,
  and duplicate non-inline definitions.
- Link external entities across translation units by namespace-qualified name
  and function signature, while preserving internal entities from `static` and
  unnamed namespaces as distinct.
- Evaluate PA8 constant expressions from typed state, including integral
  constants, constexpr pointers to static objects/functions, array-to-pointer
  and function-to-pointer conversions, references, `true`, `false`, `nullptr`,
  and literals.
- Lower initializers into byte vectors plus relocatable entity references.
  References use pointer representation and lifetime-extended temporaries are
  stored as separate image objects.
- Plan the PA8 image in three blocks:
  1. linked variables and functions in first declaration order;
  2. lifetime-extended temporaries in first use order;
  3. string literal objects in token order.
  Variables, temporaries, and string literal objects are aligned according to
  PA8 ABI rules before bytes are written; mock function stubs are emitted as
  four bytes in first-declaration order with the reference-compatible image
  placement used by the PA8 oracle.

## Architecture Review

The implementation is a standalone `nsinit` layer in `dev/src` and does not
route through reference tools, host compilers, interpreters, VMs, generated
payloads, or copied runtime images.  `dev/nsinit.cpp` only validates the PA8
`-o outfile src...` shape and calls `nsinit::compile_to_file`, which runs
preprocessing, checked post-token collection, PA8 parsing, program linking,
initializer analysis, and image emission.

The current ownership boundary is explicit: each `TranslationUnit` owns its
namespace tree, entities, and string literals; `Program` owns linked entities
and lifetime-extended temporaries.  Expressions carry typed lookup context,
string literal pointers, and qualified names; image-time initializers carry
bytes plus relocatable entity/string/temporary targets and a `constant` bit for
constexpr enforcement.  `thread_local` is represented separately from
`static`/`extern` linkage so specifier order does not change linked identity.

The audit found initializer lowering was doing too much recovery from "no
constant value" by silently emitting zero for invalid conversions.  That has
been replaced with typed compatibility checks for references, pointers,
fundamental conversions, arrays, string literals, and constexpr variables.
Nonconstant but well-formed initializers remain representable as zero or
relocatable image bytes as required by PA8; invalid initializers now diagnose
instead of falling through.

Performance remains bounded by straightforward program-size walks: parsing is
single pass per translation unit, linking is a map lookup per entity, image
layout is a linear walk of the three output blocks, and initializer lowering
evaluates only the expression being lowered.  Name lookup can recurse through
using directives, but it tracks visited namespaces and is not used as a
repeated full-program scan.

## Validation

- Iterate with `make test-report ACTIVE_TEST_REPORT_PAS='pa8'` for focused
  diagnostics.
- After meaningful parser, semantic, linker, or image changes, run
  `make test-report-through-pa8`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa8 --paths dev/src`.
- Commit cohesive progress only after the required checks pass.

## Final Architecture Review

PA8 now has the required staged compiler path with no skipped phases or
fallback success path for ill-formed grammar-valid initializers.  The audit
cleanup tightened `dev/src/nsinit_image.cpp`, `dev/src/nsinit_parser.cpp`,
`dev/src/nsinit_model.cpp`, and `dev/src/nsinit_internal.h` while preserving
PA7 and earlier tools through separate source-set ownership.

The final image path is: linked variable/function selection in
`link_program`, typed initializer lowering and constexpr validation in
`analyze_program_initializers`, deterministic layout of entities,
temporaries, and string literals in `layout_program`, and byte/relocation
writing in `write_program_image`.  The implementation has focused course PA8
regressions for the audited edge cases and passes the required through-PA8
report and file audit.
