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
  Each object is aligned according to PA8 ABI rules before bytes are written.

## Validation

- Iterate with `make test-report ACTIVE_TEST_REPORT_PAS='pa8'` for focused
  diagnostics.
- After meaningful parser, semantic, linker, or image changes, run
  `make test-report-through-pa8`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa8 --paths dev/src`.
- Commit cohesive progress only after the required checks pass.
