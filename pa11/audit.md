## Audit Plan

Target: PA11 full-stage audit for `cppgm++ --emit-types`.

Files to inspect:

- `dev/cppgm++.cpp` for driver dispatch, required command-line shape, and
  absence of fallback success paths.
- `dev/frontend_source_sets.mk` for PA11 source registration in the `cppgm++`
  tool only.
- `dev/src/pa11_types.h`, `dev/src/pa11_internal.h`,
  `dev/src/pa11_model.cpp`, `dev/src/pa11_parser.cpp`, and
  `dev/src/pa11_emit.cpp` for the semantic model, parser/analyzer, ownership
  boundaries, lookup/type construction, constant evaluation, and deterministic
  emission.
- PA11 tests under `pa11/tests/` and any course PA11 tests under
  `cppgm.tests/course/pa11/` for coverage shape and risk areas.
- Recent PA11 commit history to distinguish intended implementation from audit
  cleanup.

Ownership boundaries to verify:

- The PA11 model owns scopes, namespace aliases, using directives, bindings,
  canonical types, enum values, and supported constant values directly instead
  of recovering facts from emitted text.
- Reopened namespaces reuse semantic scopes while class, enum, function, block,
  and template-parameter scopes remain ordered children of their declaring
  scope.
- Types, declarations, and lookup targets use stable semantic objects or
  canonical type structures rather than duplicated string-only facts.
- The `--emit-types` driver path stays independent of PA10 `--emit-ast`
  output, reference binaries, host compilers, template binaries, embedded
  payloads, interpreters, VMs, or runtime substitutes.

Performance risks to inspect:

- Qualified and unqualified lookup through namespaces, using directives,
  classes, enum scopes, and aliases for repeated full-tree walks or avoidable
  quadratic scans.
- Declarator parsing, token range handling, and constant-expression evaluation
  for excessive copying or hot-path reparsing.
- Deterministic emission for repeated sorting, hidden global scans, or
  recomputation of formatted type strings where semantic objects already exist.
- Multi-translation-unit handling for unintended shared mutable state or
  repeated whole-suite behavior.

File-audit and bypass checks:

- Confirm all new implementation files are under `dev/src` and are listed in
  `dev/frontend_source_sets.mk` when needed.
- Search for skipped phases, dummy/minimal outputs, test-specific gates,
  timeout workarounds, embedded fixture/output payloads, calls to reference
  binaries, host compiler shell-outs, or code moved to unchecked paths.
- Run `perl scripts/cppgm_file_audit.pl --stage pa11 --paths dev/src` after
  cleanup.

## Findings

- **Block-scope declaration recovery could hide semantic failures.**
  `parse_block_item` caught every declaration parse exception and skipped the
  token sequence as a statement.  That allowed declaration-shaped block items
  such as invalid arrays to succeed silently after semantic analysis had already
  committed to a declaration.
- **Anonymous enum output used empty semantic names.**  Anonymous enum
  specifiers were routed through named enum binding creation, producing empty
  `type  enum ` and `enum ` spellings instead of a deterministic anonymous type
  identity.
- **Anonymous class and struct names used the union prefix.**  Anonymous record
  specifiers all reused the `__anonymous_union_type__` spelling.  Anonymous
  unions matched the existing reference, but class and struct identities were
  misleading.
- **Template-template parameter inner names leaked.**  Named parameters inside a
  template-template parameter list were added to the enclosing template
  parameter scope, making those inner names visible in the following
  declaration body.
- **Enumerator initializers did not require a valid constant expression.**  A
  failed expression parse could leave the initializer value at zero and still
  add the enumerator binding.
- **The PA11 parser exceeded the file-audit source limit after cleanup.**
  Splitting stateless declaration-specifier helpers was required to keep the
  implementation under the audited file-size boundary without weakening the
  check.
- **The required through-stage report exposed older-stage timeout blockers.**
  PA3 `300-triple.t` exceeded the default text-test timeout through per-line
  stream overhead, and PA9 `300-binary-calculator.t.1` exceeded the default
  generated-program timeout because label memory operands emitted an absolute
  address load before each global access.
- No skipped PA10 syntax boundary, dummy/minimal output path, shell-out to
  reference binaries or host compilers, interpreter/VM/trampoline/template
  binary substitute, embedded output payload, fixture-name gate, file-audit
  bypass, or hidden unchecked PA11 implementation fragment was found.

## Changes Made

- Added committed-declaration tracking in `dev/src/pa11_parser.cpp` so block
  item fallback is limited to truly ambiguous expression statements; committed
  declaration failures now propagate.
- Added deterministic anonymous type naming helpers.  Anonymous unions keep the
  existing `__anonymous_union_type__` reference-compatible spelling; anonymous
  classes, structs, and enums now use kind-specific generated names.
- Changed anonymous enum construction to create a semantic enum type without
  adding an impossible named-type binding, while preserving unscoped enumerator
  injection into the current scope.
- Parsed template-template parameter clauses in an isolated temporary parameter
  scope so inner parameter names do not leak outward.
- Required explicit enum initializer expressions to evaluate successfully before
  storing `constant_value`.
- Split PA11 declaration-specifier helper logic into
  `dev/src/pa11_support.cpp` and registered `pa11_support` in
  `dev/frontend_source_sets.mk`.
- Added PA11 course regressions for anonymous class, struct, and enum typedefs,
  invalid block declaration recovery, invalid enum initializers, and
  template-template inner-name scope leakage.
- Fixed older-stage timeout blockers found by the required through report:
  `ctrlexpr` now disables synced iostreams and buffers its output until EOF,
  and `cy86` emits RIP-relative x86-64 loads/stores for label-addressed memory
  operands instead of loading the label address into a scratch register first.

## Validation

- Focused PA11 report passed:
  `make test-report ACTIVE_TEST_REPORT_PAS='pa11'`
  reported `55 / 55` tests passing.
- Focused timeout regression report passed:
  `make test-report ACTIVE_TEST_REPORT_PAS='pa3 pa9'`
  reported `32 / 32` tests passing.
- Required through-stage report passed:
  `make test-report-through-pa11`
  reported `544 / 544` tests passing across PA1 through PA11.
- Required file audit passed:
  `perl scripts/cppgm_file_audit.pl --stage pa11 --paths dev/src`
  exited 0.  It reported four non-fatal warnings: three existing
  nsdecl/nsinit structural warnings and one PA11 model similarity warning to the
  earlier semantic type helpers; no file-audit fatal, source-set omission,
  hidden fragment, or bypass remained.
