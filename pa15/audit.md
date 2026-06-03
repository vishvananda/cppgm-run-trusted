# PA15 Audit

## Audit Plan

Review the PA15 full-stage implementation against `pa15/README.md`,
`pa15/plan.md`, the PA15 commits `cbf4d50` and `ae3286c`, and the changed
implementation files under `dev/src/`.

Files to inspect:

- `dev/src/pa11_internal.h`, `dev/src/pa11_model.cpp`, and
  `dev/src/pa11_support.cpp` for class type metadata ownership, layout facts,
  and compatibility with earlier PA11 type dumping behavior.
- `dev/src/pa12_internal.h`, `dev/src/pa12_model.cpp`,
  `dev/src/pa12_decls.cpp`, `dev/src/pa12_records.cpp`,
  `dev/src/pa12_types.cpp`, `dev/src/pa12_names.cpp`,
  `dev/src/pa12_expr.cpp`, `dev/src/pa12_expr_nodes.cpp`,
  `dev/src/pa12_expr_semantics.cpp`, `dev/src/pa12_statements.cpp`, and
  `dev/src/pa12_support.cpp` for semantic representation of members, `this`,
  constructors/destructors, access control, single inheritance, aggregate
  initialization, bit-fields, and lifetime actions.
- `dev/src/pa14_lowir_internal.h`, `dev/src/pa14_lowir.cpp`,
  `dev/src/pa14_lowir_call.cpp`, `dev/src/pa14_lowir_expr.cpp`,
  `dev/src/pa14_lowir_init.cpp`, `dev/src/pa14_lowir_program.cpp`, and
  `dev/src/pa14_lowir_support.cpp` for LowIR lowering of object storage,
  field/member projections, ctor/dtor helpers, namespace-scope lifetime, and
  deterministic output without fallback payloads.
- `dev/frontend_source_sets.mk` for source-list coverage of new PA14 lowering
  files.
- PA15 test inputs under `pa15/tests/general/` and `pa15/tests/spec/`, plus
  course tests under `cppgm.tests/course/pa15/`, to confirm the implementation
  is not keyed to individual fixture names or narrow source shapes.

Performance risks to inspect:

- repeated full record/member scans in expression lowering, constructor
  emission, and aggregate initialization hot paths;
- avoidable copying of class layout, member, and action vectors;
- repeated recomputation of mangled LowIR names or helper bodies;
- nested initializer/member lookup loops that could become quadratic on large
  class or aggregate tests.

Ownership boundaries to inspect:

- `Type`/record metadata remains the owner of layout facts; LowIR lowering must
  consume offsets and sizes from semantic state rather than parse display names;
- member lookup and access decisions stay in PA12 semantic bindings rather than
  being recovered downstream from strings;
- constructor/destructor action plans are represented as compiler data and
  emitted on demand, without duplicated helper ownership between PA12 and PA14;
- namespace-scope startup/shutdown emission is driven by semantic lifetime
  requirements, not by file names or test-specific conditions.

File-audit issues to inspect:

- new `dev/src/*.cpp` files are listed in `dev/frontend_source_sets.mk`;
- no hidden implementation fragments live outside `dev/` or `dev/src/`;
- no file-size/file-audit bypasses, weakened checks, embedded payloads, copied
  runtimes, interpreter/VM/trampoline paths, or shell-outs to reference tools
  are present.

## Findings

- No skipped compiler phase, fallback success path, dummy LowIR generation,
  interpreter/VM/trampoline/template-binary path, embedded payload, reference
  binary shell-out, timeout workaround, or PA15 fixture-name gate was found in
  the audited PA15 implementation surface.
- Class/object facts are represented in compiler-owned state. PA11 `Type`
  records own layout facts and cache them with `layout_valid`; PA12 `Binding`
  objects carry static/member/access/friend/bit-field/lifetime facts; PA14
  lowering consumes node bindings, selected direct calls, and member offsets
  instead of recomputing field identity from source text.
- Performance-sensitive PA15 paths are bounded by local member, initializer, or
  direct-base walks. Helper emission is keyed by binding/layout state and
  generated-helper sets, so the audit did not find repeated full-suite walks,
  repeated whole-program scans, or avoidable hot-path recomputation blockers.
- `dev/frontend_source_sets.mk` includes the new PA14 lowering files:
  `pa14_lowir_call`, `pa14_lowir_expr`, and `pa14_lowir_init`.
- File audit passes for `pa15 --paths dev/src`. The warnings are structural
  warnings about large shared internal headers and legacy duplication in
  earlier namespace-model code; they are not unchecked PA15 implementation
  fragments, hidden payloads, or weakened audit checks.
- No architecture, performance, cheating, regression, or file-audit blocker was
  found that required a semantic change.

## Changes Made

- Cleaned misleading indentation in PA12 declaration, record-helper, support,
  and class-body parsing code so initializer/catch/layout-invalidating blocks
  visually match their actual control flow.
- Cleaned misleading indentation in PA14 loop, aggregate-initialization,
  object-initialization, member-initialization, and pending-inline-emission
  lowering code. These edits are behavior-preserving readability cleanup for
  the PA15 object-lifetime surface.
- Updated `pa15/plan.md` with `Architecture Review` and
  `Final Architecture Review` sections grounded in the current implementation.

## Validation

- `make build` passed.
- `make test-pa15` passed: 167/167 local PA15 tests and 0/0 course PA15 tests.
- `make test-report-through-pa15` passed: 1006/1006 tests through PA15.
- `perl scripts/cppgm_file_audit.pl --stage pa15 --paths dev/src` passed with
  6 warnings. The warnings were:
  `dev/src/nsinit_internal.h`, `dev/src/pa12_internal.h`, and
  `dev/src/pa14_lowir_internal.h` large-header structure warnings;
  duplicate-block warnings for `nsinit_model.cpp`/`nsdecl_model.cpp`,
  `nsinit_parser.cpp`/`nsdecl_parser.cpp`, and
  `pa11_model.cpp`/`nsinit_model.cpp`.
