# PA12 Audit

## Audit Plan

Inspect the PA12 implementation against the handout, `pa12/plan.md`, and the
PA12 implementation commit. The audit will cover these files:

- Driver and build wiring: `dev/cppgm++.cpp`,
  `dev/frontend_source_sets.mk`, and `dev/src/pa12_semantics.h`.
- PA11 ownership and lookup integration touched by PA12:
  `dev/src/pa11_internal.h` and `dev/src/pa11_model.cpp`.
- PA12 semantic state and dump model: `dev/src/pa12_internal.h`,
  `dev/src/pa12_model.cpp`, `dev/src/pa12_support.cpp`, and
  `dev/src/pa12_records.cpp`.
- PA12 declarations, lookup, and local scopes: `dev/src/pa12_decls.cpp`,
  `dev/src/pa12_names.cpp`, and `dev/src/pa12_statements.cpp`.
- PA12 expression typing, conversions, calls, and pointer handling:
  `dev/src/pa12_expr.cpp`, `dev/src/pa12_expr_semantics.cpp`,
  `dev/src/pa12_expr_nodes.cpp`, `dev/src/pa12_expr_pointer.cpp`, and
  `dev/src/pa12_types.cpp`.
- Regression coverage from PA10 and PA11 driver modes, because PA12 reuses the
  parser, canonical type spelling, and scope/type model.

Check for skipped compiler phases, fallback success paths, dummy or minimal
semantic output, test-specific source-shape gates, runtime/interpreter/trampoline
substitutes, embedded payloads, and any reference-tool or host-compiler calls in
the implementation. Confirm semantic facts are carried by typed structures
instead of recovered from dump strings.

Performance risks to inspect are repeated full-scope or full-translation-unit
walks in lookup and overload resolution, unnecessary copying of type and
expression records on hot paths, recursive statement/expression traversal with
quadratic child scans, and any timeout-oriented special casing.

Ownership boundaries to inspect are PA11 declaration/type ownership versus PA12
semantic-state references, expression-node lifetimes, function-body local scope
lifetimes, overload-candidate storage, and deterministic dump ordering across
translation units and namespaces.

File-audit issues to inspect are oversized or hidden implementation fragments,
new source files missing from `dev/frontend_source_sets.mk`, unchecked generated
or moved code, weakened audit checks, and implementation outside `dev/` or
`dev/src/`.

## Findings

- Found stringly semantic recovery in the PA12 expression layer:
  `__builtin_constant_p` was recognized by searching the formatted callee dump
  line, constant-argument detection walked rendered `Node::line` strings, and
  braced initializer handling checked for the literal dump line
  `braced-init-list`.
- Found dummy or incomplete constant facts: explicit enum initializers were
  ignored unless they were a single literal token, and nonliteral array bounds
  were parsed but forced to bound `1`.
- Found a fallback success path in compound assignment: when RHS conversion
  failed for compound assignments, the expression was still accepted and printed
  using the original RHS node.
- Found a call-semantics gap for calls through function pointers or function
  references: the implementation checked arity but did not apply fixed-parameter
  conversions or reject invalid argument conversions.
- Found an over-permissive pointer conversion: object pointers could convert to
  unqualified `void*` even when the source pointee was cv-qualified.
- Inspected driver/build wiring, source-set membership, PA11 integration,
  lookup, ownership, and file-audit output. No reference-tool calls,
  host-compiler calls, process execution, fixture-path gates, timeout gates,
  embedded payloads, interpreter/VM/trampoline substitutes, unchecked source
  movement, or source files missing from `dev/frontend_source_sets.mk` were
  found.

## Changes Made

- Added typed PA12 expression facts for constant expressions, integer constant
  values, builtin identity, and braced-initializer identity.
- Replaced dump-string inspection in `__builtin_constant_p` and braced
  initializer handling with those typed facts.
- Evaluated PA12 enum initializers and array bounds through typed expression
  constant values, and made `sizeof` produce a constant semantic value while
  preserving the existing dump shape.
- Stored const/constexpr variable constant facts when initialization produces a
  typed constant value, so later id-expressions can use the semantic binding
  instead of recomputing from output text.
- Applied parameter conversions for calls through function pointers and
  function references.
- Tightened assignment semantics by rejecting non-modifiable lvalues and
  invalid compound-assignment RHS categories.
- Tightened pointer conversion to require cv preservation when converting
  object pointers to `void*`.
- Added PA12 course regressions for invalid function-pointer argument
  conversion, invalid compound-assignment RHS conversion, invalid cv-dropping
  `const T*` to `void*`, and enum/array-bound constant propagation.
- Removed unused PA12 declarations/helpers found during the audit sweep.

## Validation

- `make build` passed.
- `make test-pa12` passed: 126 local PA12 tests and 4 PA12 course tests.
- `make test-report-through-pa12` passed: 674/674 tests across PA1 through
  PA12.
- `perl scripts/cppgm_file_audit.pl --stage pa12 --paths dev/src` passed with
  exit status 0. The reported warnings were inspected and did not indicate
  hidden implementation fragments, file-audit bypasses, or unchecked code paths.
