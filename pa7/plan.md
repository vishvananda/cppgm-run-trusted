# PA7 nsdecl Implementation Plan

## Design

- Keep PA7 on the existing frontend path: preprocess each source file with
  `preproc_support`, convert phase-7 posttokens with `posttoken_pipeline`, and
  parse the PA7 grammar in-process.
- Add PA7-owned support under `dev/src/` and link it only into `nsdecl`.
  `dev/nsdecl.cpp` should remain the command-line wrapper and output writer.
- Model semantic facts explicitly:
  - `Type` values for fundamental, cv-qualified, pointer, reference, array, and
    function types.
  - `Entity` values for namespaces, typedef/alias names, variables, functions,
    namespace aliases, using declarations, and using directives.
  - `Namespace` owns its child namespaces and ordered reportable declarations.
- Parse declarations directly with semantic actions. Namespace definitions push
  the current namespace, simple declarations build one base type and apply each
  declarator, and typedef / alias declarations enter type aliases without
  emitting report lines.
- Implement namespace lookup from typed state, not from formatted report text:
  unqualified lookup searches the current namespace chain plus using directives
  and inline/unnamed namespace exposure; qualified lookup walks namespace/alias
  components and resolves the final name under the requested entity kind.
- Apply PA7 type rules during construction:
  canonical fundamental type spelling, cv combination, typedef substitution,
  reference collapsing, function parameter adjustment for arrays/functions,
  `void` parameter list normalization, variadic functions, and array bounds from
  integer literals.

## Ownership Boundaries

- `dev/src/nsdecl_support.*`: public entry point and report model.
- Parser internals stay private to the implementation files; no handout or test
  files are read by the compiler.
- Existing PA1-PA6 helpers remain unchanged except for normal source-set wiring.

## Validation

- First run focused PA7 reports with
  `make test-report ACTIVE_TEST_REPORT_PAS='pa7'`.
- After parser/semantic changes settle, run the required through check:
  `make test-report-through-pa7`.
- Run the required audit:
  `perl scripts/cppgm_file_audit.pl --stage pa7 --paths dev/src`.
- Commit cohesive implementation progress and leave `git status --short` clean.
