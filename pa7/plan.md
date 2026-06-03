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

## Architecture Review

The implementation matches the planned in-process frontend path. `dev/nsdecl.cpp`
only handles command-line parsing, output-file creation, and construction of
preprocessor options. `dev/src/nsdecl_support.cpp` emits the translation-unit
header and parses each source independently through `parse_source_file`, so PA7
does not introduce cross-translation-unit state before linkage is required by
later assignments.

PA7-owned semantic state is concentrated in `dev/src/nsdecl_internal.h`,
`dev/src/nsdecl_model.cpp`, and `dev/src/nsdecl_parser.cpp`. The model stores
types as explicit `Type` nodes for fundamental, cv-qualified, pointer,
reference, array, and function types. A `TranslationUnit` owns all `Entity`
objects, while each `Namespace` owns child namespaces and keeps separate ordered
report lists for variables, functions, and namespaces. Raw pointers in maps and
order vectors point at objects owned by `unique_ptr`, so vector movement does
not invalidate the pointed-to model objects.

Name lookup is represented as semantic state rather than recovered from output
text. Namespace member maps contain owned declarations and using-declaration
imports, lookup filters by requested entity kind, and using-directive traversal
uses a visited set to avoid cycles. Unqualified lookup walks the namespace
parent chain; qualified lookup starts from the resolved namespace or namespace
alias. Unnamed namespaces and inline namespaces are exposed through the same
using-directive mechanism, including reopening an existing named namespace as
inline.

The parser consumes phase-7 posttokens produced by the existing PA1-PA6
frontend helpers. It parses PA7 declarations directly with semantic actions:
namespace definitions update namespace ownership, aliases and using declarations
enter lookup state, typedef and alias declarations enter type aliases without
report lines, and variable/function declarations are emitted from model order.
Declarators are stored as pointer prefixes, suffixes, and nested declarators,
then folded into explicit types. Type factories handle canonical spelling, array
cv propagation, function parameter adjustment, `void` parameter-list
normalization, variadics, and reference collapsing.

The source-set boundary is narrow: `dev/frontend_source_sets.mk` links the PA7
model/parser/support files only into `nsdecl`. No handout tests, reference
outputs, reference binaries, host compilers, generated payloads, or unchecked
paths are read by the compiler implementation.

## Final Architecture Review

The audit found one PA7 semantic blocker in the implemented architecture:
reopening an existing named namespace with an `inline namespace` definition
updated the namespace's inline flag but did not expose that namespace in the
parent lookup state. The model now adds the parent using-directive exposure in
that path, and `cppgm.tests/course/pa7/280-inline-reopen.t` covers the
reference behavior.

No skipped compiler phases, dummy/minimal output paths, reference-tool shell
outs, interpreter/VM/trampoline/template-binary substitutions, embedded payloads,
test-specific gates, timeout workarounds, file-audit bypasses, or hidden
implementation fragments were found in the PA7-owned implementation. Lookup uses
maps and bounded visited-set traversals instead of repeated full-suite or
whole-tree scans, and output walks the already-ordered namespace model once.

Final validation:

- `make -C pa7 check TEST=course/pa7/280-inline-reopen.t` passed.
- `make test-pa7` passed the PA7 local and course tests.
- `make test-report-through-pa7` passed, 293/293 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa7 --paths dev/src` passed, 29
  files checked.
